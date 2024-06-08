// L3-eval.ts
import { map, zip, zipObj, filter, head } from "ramda";
import { ClassExp, isCExp, isLetExp , isClassExp, isBinding} from "./L3-ast";
import { BoolExp, CExp, Exp, IfExp, LitExp, NumExp,
         PrimOp, ProcExp, Program, StrExp, VarDecl, Binding } from "./L3-ast";
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLitExp, isNumExp,
             isPrimOp, isProcExp, isStrExp, isVarRef } from "./L3-ast";
import { makeBoolExp, makeLitExp, makeNumExp, makeProcExp, makeStrExp } from "./L3-ast";
import { parseL3Exp } from "./L3-ast";
import { applyEnv, makeEmptyEnv, makeEnv, Env, isNonEmptyEnv } from "./L3-env-sub";
import { isClosure, makeClosure, Closure, Value, makeClass , Class, isClass, makeSymbolSExp, makeObject, makeObjectEnv, isObject, isSymbolSExp, Object, SymbolSExp } from "./L3-value";
import { first, rest, isEmpty, List, isNonEmptyList , allT } from '../shared/list';
import { isBoolean, isNumber, isString } from "../shared/type-predicates";
import { Result, makeOk, makeFailure, bind, mapResult, mapv } from "../shared/result";
import { renameExps, substitute } from "./substitute";
import { applyPrimitive } from "./evalPrimitive";
import { parse as p } from "../shared/parser";
import { Sexp } from "s-expression";
import { format } from "../shared/format";
import { ReadStream } from "fs";

// ========================================================
// Eval functions

const L3applicativeEval = (exp: CExp, env: Env): Result<Value> =>

    //isClassExp ? 
    isNumExp(exp) ? makeOk(exp.val) : 
    isBoolExp(exp) ? makeOk(exp.val) :
    isStrExp(exp) ? makeOk(exp.val) :
    isPrimOp(exp) ? makeOk(exp) :
    isVarRef(exp) ? applyEnv(env, exp.var) :
    isLitExp(exp) ? makeOk(exp.val) :
    isIfExp(exp) ? evalIf(exp, env) :
    isProcExp(exp) ? evalProc(exp, env) :
    isAppExp(exp) ? bind(L3applicativeEval(exp.rator, env), (rator: Value) =>
                        bind(mapResult(param => 
                            L3applicativeEval(param, env), 
                              exp.rands), 
                            (rands: Value[]) =>
                                //isClass(raator) ? apllyMethod
                                L3applyProcedure(rator, rands, env))) :
    isLetExp(exp) ? makeFailure('"let" not supported (yet)') :
    isClassExp(exp) ? evalClass(exp,env):
    makeFailure('Never');


//ADDED:
const evalClass = (cls: ClassExp, env: Env) : Result<Class> =>
    //allT(isBinding,cls.methods)? 
    allT(isProcExp,map((m) => m.val,cls.methods)) ?
    makeOk(makeClass(cls.fields, map((method : Binding) => ({var: method.var, val : method.val as ProcExp}), cls.methods))) : 
    makeFailure("bad stuff happened");
    //fields: VarDecl[], methods:{var:VarDecl, val:ProcExp}[]

export const isTrueValue = (x: Value): boolean =>
    ! (x === false);

const evalIf = (exp: IfExp, env: Env): Result<Value> =>
    bind(L3applicativeEval(exp.test, env), (test: Value) => 
        isTrueValue(test) ? L3applicativeEval(exp.then, env) : 
        L3applicativeEval(exp.alt, env));

const evalProc = (exp: ProcExp, env: Env): Result<Closure> =>
    makeOk(makeClosure(exp.args, exp.body));

//ADDED: 
const createMapFromLists = (l1: any[], l2: any[]): { [key: string]: any } => {
    // if (l1.length !== l2.length) {
    //     throw new Error("Both lists must be of the same length");
    // }

    const result: { [key: string]: any } = {};

    for (let i = 0; i < l1.length; i++) {
        result[l1[i]] = l2[i];
    }

    return result;
}

const fieldsMaker = (vr: VarDecl[], vl:Value[]) : ({var:VarDecl, val:Value}[]) => {
    return vr.map((variable, index) => ({
        var: variable,
        val: vl[index]
    }));
}

const L3applyProcedure = (proc: Value, args: Value[], env: Env): Result<Value> =>
    isPrimOp(proc) ? applyPrimitive(proc, args) :
    isClosure(proc) ? applyClosure(proc, args, env) :
    isClass(proc) && !isNonEmptyEnv(env)? makeOk(makeObjectEnv(fieldsMaker(proc.fields,args), 
                    map((method: {var: VarDecl, val:ProcExp}) => ({var: makeSymbolSExp(method.var.var), val: makeClosure(method.val.args, method.val.body)}),proc.methods)
                    ,env)) :
    isClass(proc)? makeOk(makeObject(fieldsMaker(proc.fields,args), 
                    map((method: {var: VarDecl, val:ProcExp}) => ({var: makeSymbolSExp(method.var.var), val: makeClosure(method.val.args, method.val.body)}),proc.methods))) :
    isObject(proc) ? applyObject(proc,args,env):
    makeFailure(`Bad procedure ${format(proc)}`);

// Applications are computed by substituting computed
// values into the body of the closure.
// To make the types fit - computed values of params must be
// turned back in Literal Expressions that eval to the computed value.
const valueToLitExp = (v: Value): NumExp | BoolExp | StrExp | LitExp | PrimOp | ProcExp =>
    isNumber(v) ? makeNumExp(v) :
    isBoolean(v) ? makeBoolExp(v) :
    isString(v) ? makeStrExp(v) :
    isPrimOp(v) ? v :
    isClosure(v) ? makeProcExp(v.params, v.body) :
    makeLitExp(v);

const applyClosure = (proc: Closure, args: Value[], env: Env): Result<Value> => {
    const vars = map((v: VarDecl) => v.var, proc.params);
    const body = renameExps(proc.body);
    const litArgs : CExp[] = map(valueToLitExp, args);
    return evalSequence(substitute(body, vars, litArgs), env);
    //return evalSequence(substitute(proc.body, vars, litArgs), env);
}

//ADDED
const resultFromNullable = <T>(value: T | undefined, errorMessage: string): Result<T> =>
    value !== undefined ? makeOk(value) : makeFailure(errorMessage);

const createNewEnv = (fields: { var: VarDecl, val: Value }[], baseEnv: Env): Env => {
    return fields.reduce((env, field) => makeEnv(field.var.var, field.val, env), baseEnv);
}

const applyObject = (proc: Object, args: Value[], env: Env): Result<Value> => {
    if (isEmpty(args)) {
        return makeOk(proc);
    }

    if (!isSymbolSExp(args[0])) {
        return makeFailure("no symbol detected for method apply");
    }

    const method = head(filter((method: { var: SymbolSExp, val: Closure }) => method.var.val === (args[0] as SymbolSExp).val, proc.methods));
    const env2 = createNewEnv(proc.fields,env);

    return bind(resultFromNullable(method, `Unrecognized method: ${args[0].val}`), (foundMethod) =>
        applyClosure(foundMethod.val, args.slice(1), env2)
    );
    /*
    !isNonEmptyList(args) ? makeOk(proc):
    !isSymbolSExp(args[0]) ? makeFailure("no symbol detected for method apply"):
    bind(
        resultFromNullable(head(filter((method: { var: SymbolSExp, val: Closure }) => method.var.val === (args[0] as SymbolSExp).val, proc.methods)),"no matching method"),
        (method:{ var: SymbolSExp, val: Closure}) => applyClosure(method.val, args.slice(1), env)
    );
    // bind(head(filter((method:{var:SymbolSExp, val:Closure}) => method.var === args[0], proc.methods)),
    //         (method) => method ? applyClosure(method.val, args.slice(1), env) : makeFailure("no matching method")) ;
        // applyClosure((filter((method:{var:SymbolSExp, val:Closure}) => method.var === args[0], proc.methods))[0].val, args.slice(1),env):
        // makeFailure("no matching method")*/
}

// Evaluate a sequence of expressions (in a program)
export const evalSequence = (seq: List<Exp>, env: Env): Result<Value> =>
    isNonEmptyList<Exp>(seq) ? 
        isDefineExp(first(seq)) ? evalDefineExps(first(seq), rest(seq), env) :
        evalCExps(first(seq), rest(seq), env) :
    makeFailure("Empty sequence");

const evalCExps = (first: Exp, rest: Exp[], env: Env): Result<Value> =>
    isCExp(first) && isEmpty(rest) ? L3applicativeEval(first, env) :
    isCExp(first) ? bind(L3applicativeEval(first, env), _ => 
                            evalSequence(rest, env)) :
    makeFailure("Never");

// Eval a sequence of expressions when the first exp is a Define.
// Compute the rhs of the define, extend the env with the new binding
// then compute the rest of the exps in the new env.
const evalDefineExps = (def: Exp, exps: Exp[], env: Env): Result<Value> =>
    isDefineExp(def) ? bind(L3applicativeEval(def.val, env), 
                            (rhs: Value) => 
                                evalSequence(exps, 
                                    makeEnv(def.var.var, rhs, env))) :
    makeFailure(`Unexpected in evalDefine: ${format(def)}`);

// Main program
export const evalL3program = (program: Program): Result<Value> =>
    evalSequence(program.exps, makeEmptyEnv());

export const evalParse = (s: string): Result<Value> =>
    bind(p(s), (sexp: Sexp) => 
        bind(parseL3Exp(sexp), (exp: Exp) =>
            evalSequence([exp], makeEmptyEnv())));
