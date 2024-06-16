import { ClassExp, ProcExp, makeProgram, Exp, isExp, isClassExp, isIfExp,isAtomicExp ,
    Program, makeProcExp, Binding, makeIfExp, VarDecl, makeVarDecl, makeBoolExp, makeVarRef,
     makeStrExp, CExp, isProgram, makePrimOp, makeAppExp, 
     isProcExp, isLitExp, isLetExp,
     makeLetExp, isAppExp,
     makeBinding, makeLitExp,
     isDefineExp, isPrimOp,
     makeDefineExp} from "./L3-ast";
import { Result, makeFailure, makeOk } from "../shared/result";
import { map, reduce } from "ramda"

/*
Purpose: Transform ClassExp to ProcExp
Signature: class2proc(classExp)
Type: ClassExp => ProcExp
*/
export const class2proc = (exp: ClassExp): ProcExp =>{
    const symbol :VarDecl =  makeVarDecl("msg");
    return makeProcExp(exp.fields,
        [makeProcExp([symbol],
            [reduce((acc,crr)=>makeIfExp(makeAppExp(makePrimOp("eq?"),[makeVarRef("msg"), makePrimOp("'"+crr.var.var)]), makeAppExp(crr.val, []) as CExp, acc) as CExp,
            makeBoolExp(false) as CExp,
            exp.methods.reverse()
            )])as CExp
        ])
}


/*
Purpose: Transform all class forms in the given AST to procs
Signature: lexTransform(AST)
Type: [Exp | Program] => Result<Exp | Program>
*/
const lexTransformRec = (exp: Exp | Program): Exp | Program =>
    isProgram(exp)? makeProgram(map((e:Exp)=>lexTransformRec(e) as Exp,exp.exps)):
    isClassExp(exp)? class2proc(exp) as CExp :
    isIfExp(exp)? makeIfExp(lexTransformRec(exp.test) as CExp,lexTransformRec(exp.then) as CExp, lexTransformRec(exp.alt) as CExp)  as CExp:
    isProcExp(exp)? makeProcExp(exp.args, map((e)=>lexTransformRec(e),exp.body) as CExp[]):
    isAtomicExp(exp)? exp as CExp:
    isLitExp(exp) ? exp as CExp:
    isLetExp(exp) ? makeLetExp(map((b)=>makeBinding(b.var.var,lexTransformRec(b.val) as CExp),exp.bindings),
                                map((c)=>lexTransformRec(c) as CExp,exp.body)):
    isAppExp(exp)? makeAppExp(lexTransformRec(exp.rator) as CExp,map((c)=>lexTransformRec(c) as CExp,exp.rands)):
    isDefineExp(exp)? makeDefineExp(exp.var,lexTransformRec(exp.val) as CExp):
    makeBoolExp(false);



export const lexTransform = (exp: Exp | Program): Result<Exp | Program> =>{
    const ans = lexTransformRec(exp);
    return ans === undefined?  makeFailure("bad stuff") : makeOk(ans);
}

