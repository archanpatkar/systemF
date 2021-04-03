// Type checker
// Based on -
// https://www.cl.cam.ac.uk/teaching/1415/L28/lambda.pdf
// https://crypto.stanford.edu/~blynn/lambda/systemf.html
// https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture22.pdf

// Dep
const { equal } = require("saman");
const { sum, tagged } = require("styp");

// Type Defs
const Type = sum("Types", {
    TVar: ["v"],
    TCon: ["name"],
    TArr: ["t1", "t2"]
});

const Scheme = sum("Scheme", {
    Forall: ["var", "type"]
});

const TNumber = Type.TCon("number");
const TBool = Type.TCon("bool");
const TUnit = Type.TCon("unit");

const PrimTypes = {
    "number":TNumber,
    "bool":TBool,
    "unit":TUnit
};

const optypes = {
    "ADD": Type.TArr(TNumber,Type.TArr(TNumber,TNumber)),
    "MUL": Type.TArr(TNumber,Type.TArr(TNumber,TNumber)),
    "SUB": Type.TArr(TNumber,Type.TArr(TNumber,TNumber)),
    "DIV": Type.TArr(TNumber,Type.TArr(TNumber,TNumber)),
    "AND": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "OR": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "GT": Type.TArr(TNumber,Type.TArr(TNumber,TBool)),
    "LT": Type.TArr(TNumber,Type.TArr(TNumber,TBool)),
    "NOT": Type.TArr(TBool,TBool),
    "NEG": Type.TArr(TNumber,TNumber),
    "EQ": Scheme.Forall(
        [Type.TVar("o1")],
        Type.TArr(Type.TVar("o1"),Type.TArr(Type.TVar("o1"),TBool))
    )
}

function convertType(type) {
    if(type === "int") return TNumber;
    if(type === "bool") return TBool;
    if(type === "unit") return TUnit;
    if(typeof type === "string") return Type.TVar(type);
    if(Array.isArray(type)) return Type.TArr(convertType(type[0]),convertType(type[0]));
}

function printType(type,level=0) {
    return Type.is(type) ?
        type.cata({
            TCon: ({ name }) => name,
            TVar: ({ v }) => v,
            TArr: ({ t1, t2 }) => {
                return `${level%3?"(":""}${printType(t1,level+1)} -> ${printType(t2,level+1)}${level%3?")":""}`;
            }
        }):
        Scheme.is(type) && type.var.length ?
        `forall ${type.var.map(e => printType(e)).join(" ")}. ${printType(type.type)}`:
        printType(type.type)
}

// Errors
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable --> '${name}' not in Scope`);
const defInScope = (name) => genericError(`Cannot redefine Variable: '${name}'`);
const notType = (type,msg) => genericError(`Expected type '${printType(type)}' ${msg}`);
const notAType = (type) => genericError(`Expected a type`);
const typeMismatch = (type1,type2) => genericError(`Couldn't match the expected type: ${printType(type1)} with type: ${printType(type2)}`);
const nonFunction = (type) => genericError(`Tried to apply to non-Function type --> ${type}`);
const nonGenFunction = (type) => genericError(`Not ${printType(type)} a Generic / Type Lambda`);

class TypeEnv {
    constructor(parent) {
        this.env = {};
        this.parent = parent;
    }

    exists(name) {
        if (this.env[name]) return this.env[name];
        else if (this.parent) return this.parent.lookUp(name);
        return false;
    }

    addBinding(name, type) {
        if(name in env) defInScope(name);
        this.env[name] = type;
    }

    removeBinding(name) {
        delete this.env[name]
    }

    lookUp(name) {  
        if (this.env[name]) return this.env[name];
        if (this.parent) return this.parent.lookUp(name);
        notInScope(name);
    }
}

class TypeChecker {
    constructor() {
        this.env = new TypeEnv(null);
        this.tenv = new TypeEnv(null);
    }

    varInit() {
        this.names = {};
        this.count = 0;
        for(let i = "a".charCodeAt(0);i < "z".charCodeAt(0);i++) {
            this.names[i-97] = [String.fromCharCode(i),0];
        }
    }

    fresh() {
        const pair = this.names[this.count++ % 25];
        let n = pair[1]++;
        return Type.TVar(`${pair[0]}${n?n:""}`);
    }

    verifyType(type) {
        return Type.is(type) || Scheme.is(type);
    }

    checkCond(ast,env) {
        const cond = this.check(ast.cond, env);
        const t1 = this.check(ast.e1, env);
        const t2 = this.check(ast.e2, env);
        if(!equal(cond,TBool)) typeMismatch(TBool,cond);
        if(!equal(t1,t2)) typeMismatch(t1,t2);
        return t1;
    }

    checkLet(ast,env) {
        const t1 = this.check(ast.e1,env);
        if(ast.e2) {
            const ne = new TypeEnv(env);
            ne.addBinding(ast.name, tdash);
            return this.check(ast.e2,ne);
        }
        env.addBinding(ast.name,t1);
        return t1;
    }

    checkTLam(ast,env) {
        const tv = convertType(ast.param);
        if(!this.verifyType(tv)) notAType(tv);
        this.tenv.addBinding(tv.v, true);
        const body = this.check(ast.body, env);
        this.tenv.removeBinding(tv.v);
        return Scheme.Forall([tv],body);
    }

    checkLam(ast,env) {
        const vt = convertType(ast.type);
        if(!this.verifyType(vt)) notAType(vt);
        const ne = new TypeEnv(env);
        ne.addBinding(ast.param, vt);
        const body = this.check(ast.body, ne);
        return Type.TArr(vt, body);
    }

    checkApp(ast,env) {
        const t1 = this.check(ast.e1, env);
        const t2 = this.check(ast.e2, env);
        if(!Type.TArr.is(t1)) nonFunction(t1);
        if(!equal(t1.t1,t2)) typeMismatch(t1.t1,t2);
        return t1.t2;
    }

    rename(scheme,map) {
        if(Type.TCon.is(scheme)) return scheme;
        if(Type.TVar.is(scheme)) return map[scheme.v];
        if(Type.TArr.is(scheme)) return Type.TArr(
            this.rename(scheme.t1,map),
            this.rename(scheme.t2,map)
        );
        if(Scheme.Forall.is(scheme)) return this.rename(scheme.type,map);
        return null;
    }

    checkTApp(ast,env) {
        const t1 = this.check(ast.tl, env);
        const t2 = convertType(ast.t);
        if(!this.verifyType(t2)) notAType(t2);
        if(!Scheme.Forall.is(t1)) nonGenFunction(t1);
        const map = {}
        map[t1.var[0].v] = t2;
        return this.rename(t1,map);
    }

    checkFix(ast,env) {
        // const t = this.infer(ast.e,env);
        // const tv = this.fresh();
        // this.addConstraint(Type.TArr(tv,tv), t);
        // this.unify(Type.TArr(tv,tv),t);
        // return this.apply(tv);
    }  

    checkUnOp(ast,env) {
        const t = this.infer(ast.v,env);
        const op = optypes[ast.op];
        if(!equal(op.t1,t)) typeMismatch(op.t1,t);
        return op.t2;
    }
    
    checkBinOp(ast,env) {
        const t1 = this.check(ast.l,env);
        const t2 = this.check(ast.r,env);
        let op = optypes[ast.op];
        if(Type.is(op)) {
            if(!equal(op.t1,t1)) typeMismatch(op.t1,t1);
            if(!equal(op.t2.t1,t2)) typeMismatch(op.t2.t1,t2);
            return op.t2.t2;
        }
        // if(Scheme.Forall.is(op)) {
        //     if(!equal(t1,t2)) typeMismatch(,t1);
        //     this.rename(scheme,)
        // }
        return TUnit;
    }

    // Pair: p => this.inferPair(p,env),
    // checkPair(ast,env) {
        // const fst = this.infer(ast.fst,env);
        // const snd = this.infer(ast.snd,env);
        // const tv = this.fresh();
        // return Type.TArr(Type.TArr(fst,Type.TArr(snd,tv)),tv);
    // }

    check(ast, env = this.env) {
        return ast.cata({
            Lit: ({ type }) => PrimTypes[type],
            Var: ({ name }) => env.lookUp(name),
            UnOp: u => this.checkUnOp(u,env),
            BinOp: b => this.checkBinOp(b,env),
            Cond: c => this.checkCond(c,env),
            Lam: l => this.checkLam(l,env),
            App: a => this.checkApp(a,env),
            Fix: f => this.checkFix(f,env),
            TApp: a => this.checkTApp(a,env),
            TLam: t => this.checkTLam(t,env),
            Let: lb => this.checkLet(lb,env)
        });
    }

    prove(ast) {
        return printType(this.check(ast))
    }
}

// (?a. \x:a->a. x) [int->int]
// (\x:int->int. x 3) (\x:int. x + 10)
module.exports = TypeChecker;