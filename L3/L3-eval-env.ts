// L3-eval.ts
// Evaluator with Environments model

import { map, filter, head  } from "ramda";
import { ClassExp, isCExp, isLetExp , isClassExp, isBinding, makeBinding} from "./L3-ast";
import { BoolExp, CExp, Exp, IfExp, LitExp, NumExp, DefineExp, LetExp,
         PrimOp, ProcExp, Program, StrExp, VarDecl, Binding , makeClassExp} from "./L3-ast";
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLitExp, isNumExp,
             isPrimOp, isProcExp, isStrExp, isVarRef } from "./L3-ast";
import { makeBoolExp, makeLitExp, makeNumExp, makeProcExp, makeStrExp } from "./L3-ast";
import { parseL3Exp } from "./L3-ast";
import { applyEnv, makeEmptyEnv, makeExtEnv, Env, isEmptyEnv} from "./L3-env-env";
import { isClosure, makeClosureEnv, Closure, Value, Class, Object, makeClass,
        makeObject, isClass, isObject, SymbolSExp,isSymbolSExp, makeSymbolSExp,
        valueToString,
        SExpValue} from "./L3-value";
import { isBoolean, isNumber, isString } from "../shared/type-predicates";
import { applyPrimitive } from "./evalPrimitive";
import { allT, first, rest, isEmpty, isNonEmptyList } from "../shared/list";
import { Result, makeOk, makeFailure, bind, mapResult } from "../shared/result";
import { parse as p } from "../shared/parser";
import { format } from "../shared/format";

// ========================================================
// Eval functions

const applicativeEval = (exp: CExp, env: Env): Result<Value> =>
    isNumExp(exp) ? makeOk(exp.val) :
    isBoolExp(exp) ? makeOk(exp.val) :
    isStrExp(exp) ? makeOk(exp.val) :
    isPrimOp(exp) ? makeOk(exp) :
    isVarRef(exp) ? applyEnv(env, exp.var) :
    isLitExp(exp) ? makeOk(exp.val) :
    isIfExp(exp) ? evalIf(exp, env) :
    isProcExp(exp) ? evalProc(exp, env) :
    isLetExp(exp) ? evalLet(exp, env) :
    isAppExp(exp) ? bind(applicativeEval(exp.rator, env),
                      (proc: Value) =>
                        bind(mapResult((rand: CExp) => 
                           applicativeEval(rand, env), exp.rands),
                              (args: Value[]) =>
                                 applyProcedure(proc, args, env))) :
    isClassExp(exp) ? evalClass(exp):
    makeFailure('"let" not supported (yet)');


//ADDED:
const evalClass = (cls: ClassExp) : Result<Class> =>
    //allT(isBinding,cls.methods)? 
    allT(isProcExp,map((m) => m.val,cls.methods)) ?
    makeOk(makeClass(cls.fields, map((method : Binding) => ({var: method.var, val : method.val as ProcExp}), cls.methods))) : 
    makeFailure("bad stuff happened");
    //fields: VarDecl[], methods:{var:VarDecl, val:ProcExp}[]


export const isTrueValue = (x: Value): boolean =>
    ! (x === false);

const evalIf = (exp: IfExp, env: Env): Result<Value> =>
    bind(applicativeEval(exp.test, env), (test: Value) => 
            isTrueValue(test) ? applicativeEval(exp.then, env) : 
            applicativeEval(exp.alt, env));

const evalProc = (exp: ProcExp, env: Env): Result<Closure> =>
    makeOk(makeClosureEnv(exp.args, exp.body, env));

//ADDED
const fieldsMaker = (vr: VarDecl[], vl:Value[]) : ({var:VarDecl, val:Value}[]) => {
    return vr.map((variable, index) => ({
        var: variable,
        val: vl[index]
    }));
}

// KEY: This procedure does NOT have an env parameter.
//      Instead we use the env of the closure making.
const applyProcedure = (proc: Value, args: Value[], env:Env): Result<Value> =>
    isPrimOp(proc) ? applyPrimitive(proc, args) :
    isClosure(proc) ? applyClosure(proc, args) :
    isClass(proc)? applyClass(proc,args,env):
    isObject(proc) ? applyObject(proc,args):
    makeFailure(`Bad procedure ${format(proc)}`);

//ADDED

const applyClass = (proc : Class, args: Value[], env:Env) : Result<Value> =>{
    const nextEnv = makeExtEnv(map((f:VarDecl)=>f.var,proc.fields),
                                map((v:Value)=> v as SExpValue,args),
                                env);
    
    return makeOk(makeObject(fieldsMaker(proc.fields,args), 
                    map((method: {var: VarDecl, val:ProcExp}) => 
                            ({var: makeSymbolSExp(method.var.var), 
                            val: makeClosureEnv(method.val.args, method.val.body, nextEnv)}),
                    proc.methods))) 
}

const applyObject = (proc: Object, args: Value[]): Result<Value> => {
    if (isEmpty(args)) {
        return makeOk(proc);
    }

    if (!isSymbolSExp(args[0])) {
        return makeFailure("no symbol detected for method apply");
    }

    const method = head(filter((method: { var: SymbolSExp, val: Closure }) => method.var.val === (args[0] as SymbolSExp).val, proc.methods));

    return method !== undefined ? applyClosure(method.val, args.slice(1)) : makeFailure(`Unrecognized method: ${args[0].val}`)
}

const applyClosure = (proc: Closure, args: Value[]): Result<Value> => {
    const vars = map((v: VarDecl) => v.var, proc.params);
    return evalSequence(proc.body, makeExtEnv(vars, args, proc.env));
}

// Evaluate a sequence of expressions (in a program)
export const evalSequence = (seq: Exp[], env: Env): Result<Value> =>
    isNonEmptyList<Exp>(seq) ? evalCExps(first(seq), rest(seq), env) : 
    makeFailure("Empty sequence");
    
const evalCExps = (first: Exp, rest: Exp[], env: Env): Result<Value> =>
    isDefineExp(first) ? evalDefineExps(first, rest, env) :
    isCExp(first) && isEmpty(rest) ? applicativeEval(first, env) :
    isCExp(first) ? bind(applicativeEval(first, env), _ => evalSequence(rest, env)) :
    first;
    
// Eval a sequence of expressions when the first exp is a Define.
// Compute the rhs of the define, extend the env with the new binding
// then compute the rest of the exps in the new env.
const evalDefineExps = (def: DefineExp, exps: Exp[], env: Env): Result<Value> =>
    bind(applicativeEval(def.val, env), (rhs: Value) => 
            evalSequence(exps, makeExtEnv([def.var.var], [rhs], env)));


// Main program
export const evalL3program = (program: Program): Result<Value> =>
    evalSequence(program.exps, makeEmptyEnv());

export const evalParse = (s: string): Result<Value> =>
    bind(p(s), (x) => 
        bind(parseL3Exp(x), (exp: Exp) =>
            evalSequence([exp], makeEmptyEnv())));

// LET: Direct evaluation rule without syntax expansion
// compute the values, extend the env, eval the body.
const evalLet = (exp: LetExp, env: Env): Result<Value> => {
    const vals  = mapResult((v: CExp) => 
        applicativeEval(v, env), map((b: Binding) => b.val, exp.bindings));
    const vars = map((b: Binding) => b.var.var, exp.bindings);
    return bind(vals, (vals: Value[]) => 
        evalSequence(exp.body, makeExtEnv(vars, vals, env)));
}
