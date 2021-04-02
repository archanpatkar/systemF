// Type checker
// Based on -
// https://www.cl.cam.ac.uk/teaching/1415/L28/lambda.pdf
// https://crypto.stanford.edu/~blynn/lambda/systemf.html
// https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture22.pdf

// Dep
const { equal } = require("saman");
const { sum, tagged } = require("saman");

// Type Defs
const Type = sum("Types", {
    TVar: ["v"],
    TCon: ["name"],
    TArr: ["t1", "t2"]
});

const Scheme = sum("Scheme", {
    Forall: ["var", "type"]
});

const TInt = Type.TCon("int");
const TBool = Type.TCon("bool");
const TUnit = Type.TCon("unit");

const PrimTypes = {
    "int":TInt,
    "bool":TBool,
    "unit":TUnit
};

const optypes = {
    "ADD": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "MUL": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "SUB": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "DIV": Type.TArr(TInt,Type.TArr(TInt,TInt)),
    "AND": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "OR": Type.TArr(TBool,Type.TArr(TBool,TBool)),
    "GT": Type.TArr(TInt,Type.TArr(TInt,TBool)),
    "LT": Type.TArr(TInt,Type.TArr(TInt,TBool)),
    "NOT": Type.TArr(TBool,TBool),
    "NEG": Type.TArr(TInt,TInt),
    "EQ": Scheme.Forall(
        [Type.TVar("o1"),Type.TVar("o2")],
        Type.TArr(Type.TVar("o1"),Type.TArr(Type.TVar("o2"),TBool))
    )
}

function convertType(type) {
    if(type === "int") return TInt;
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
const notType = (type,msg) => genericError(`Expected type '${printType(type)}' ${msg}`);
const typeMismatch = (type1,type2) => genericError(`Couldn't match the expected type: ${printType(type1)} with type: ${printType(type2)}`);
const nonFunction = (type) => genericError(`Tried to apply to non-Function type --> ${type}`);

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
        this.env[name] = type
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

    // ftv(type) {
    //     if(Type.is(type)) return type.cata({
    //         TCon: c => new Set(),
    //         TVar: ({ v }) => new Set([v]),
    //         TArr: ({ t1, t2 }) => new Set([...this.ftv(t1), ...this.ftv(t2)])
    //     });
    //     if (Scheme.is(type)) {
    //         const bounded = new Set(type.var.map(v => v.v));
    //         return new Set([...(this.ftv(type.type))].filter(v => !bounded.has(v)));
    //     }
    //     return null;
    // }

    // ftvEnv(env) {
    //     const curr = Object.values(env.env).map(t => Array.from(this.ftv(t)));
    //     if(env.parent) curr.push([...(this.ftvEnv(env.parent))]);
    //     return new Set(curr.flat());
    // }

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
        return Type.is(type) || Scheme.is(type) || this.tenv.exists(type.v);
    }

    inferLet(ast,env) {
        if (env.exists(ast.name)) defInScope(ast.name);
        const t1 = this.infer(ast.e1,env);
        const tdash = this.generalize(t1,this.applyEnv(env,this.subst));
        if(ast.e2) {
            const ne = new TypeEnv(env);
            ne.addBinding(ast.name, tdash);
            return this.infer(ast.e2,ne);
        }
        env.addBinding(ast.name,tdash);
        return tdash;
    }

    inferCond(ast,env) {
        const cond = this.infer(ast.cond, env);
        const t1 = this.infer(ast.e1, env);
        const t2 = this.infer(ast.e2, env);
        this.addConstraint(cond,TBool);
        this.addConstraint(t1, t2);
        this.unify(cond, TBool);
        this.unify(t1, t2);
        return this.apply(t1);
    }

    checkTLam(ast,env) {
        const tv = this.fresh();
        const ne = new TypeEnv(env);
        ne.addBinding(ast.param, Scheme.Forall([],tv));
        const body = this.infer(ast.body, ne);
        return this.apply(Type.TArr(tv, body));
    }

    checkLam(ast,env) {
        const tv = this.fresh();
        const ne = new TypeEnv(env);
        ne.addBinding(ast.param, Scheme.Forall([],tv));
        const body = this.infer(ast.body, ne);
        return this.apply(Type.TArr(tv, body));
    }

    checkApp(ast,env) {
        const t1 = this.infer(ast.e1, env);
        const t2 = this.infer(ast.e2, this.applyEnv(env));
        const tv = this.fresh();
        this.addConstraint(t1, Type.TArr(t2,tv));
        this.unify(this.apply(t1), Type.TArr(t2, tv));
        return this.apply(tv);
    }

    checkTApp(ast,env) {
        const t1 = this.infer(ast.e1, env);
        const t2 = this.infer(ast.e2, this.applyEnv(env));
        const tv = this.fresh();
        this.addConstraint(t1, Type.TArr(t2,tv));
        this.unify(this.apply(t1), Type.TArr(t2, tv));
        return this.apply(tv);
    }

    checkFix(ast,env) {
        const t = this.infer(ast.e,env);
        const tv = this.fresh();
        this.addConstraint(Type.TArr(tv,tv), t);
        this.unify(Type.TArr(tv,tv),t);
        return this.apply(tv);
    }  

    checkUnOp(ast,env) {
        const t = this.infer(ast.v,env);
        const tv = this.fresh();
        this.addConstraint(Type.TArr(t,tv), optypes[ast.op]);
        this.unify(Type.TArr(t,tv),optypes[ast.op]);
        return this.apply(tv);
    }
    
    checkBinOp(ast,env) {
        const t1 = this.infer(ast.l,env);
        const t2 = this.infer(ast.r,env);
        const tv = this.fresh();
        let op = optypes[ast.op];
        if(Scheme.Forall.is(op)) op = this.instantiate(op);
        this.addConstraint(Type.TArr(t1,Type.TArr(t2,tv)), op);
        this.unify(Type.TArr(t1,Type.TArr(t2,tv)),op);
        return this.apply(tv);
    }

    checkPair(ast,env) {
        const fst = this.infer(ast.fst,env);
        const snd = this.infer(ast.snd,env);
        const tv = this.fresh();
        return Type.TArr(Type.TArr(fst,Type.TArr(snd,tv)),tv);
    }

    check(ast, env = this.env) {
        if(Type.TVar.is(ast)) return this.tenv.lookUp(ast.v);
        return ast.cata({
            Lit: ({ type }) => PrimTypes[type],
            Var: ({ name }) => this.lookUp(name,env),
            Pair: p => this.inferPair(p,env),
            UnOp: u => this.inferUnOp(u,env),
            BinOp: b => this.inferBinOp(b,env),
            Let: lb => this.inferLet(lb,env),
            Cond: c => this.inferCond(c,env),
            Lam: l => this.inferLam(l,env),
            App: a => this.inferApp(a,env),
            Fix: f => this.inferFix(f,env)
        });
    }

    // check(ast) {
    //     if (ast.node == "literal") return ast.type
    //     if (ast.node == "var") return this.lookUp(ast.name)
    //     if (ops.includes(ast.node)) {
    //         const t1 = this.check(ast.l)
    //         const t2 = this.check(ast.r)
    //         if (t1 != "int" || t2 != "int") notType("int","for operands");
    //         return t1;
    //     }
    //     if(ast.node == "NEG") {
    //         const t1 = this.check(ast.val);
    //         if (t1 != "int") notType("int","for using unary '-' op");
    //         return t1;
    //     }
    //     if (ast.node == "condition") {
    //         const cond = this.check(ast.cond)
    //         if (cond != "bool") notType("bool","for 'if' condition");
    //         const t1 = this.check(ast.exp1)
    //         const t2 = this.check(ast.exp2)
    //         if (t1 != t2) generic("Expected same type for both branches");
    //         return t1;
    //     }
    //     else if (ast.node == "lambda") {
    //         this.addBinding(ast.param, ast.type);
    //         const type = this.check(ast.body);
    //         this.removeBinding(ast.param);
    //         return [ast.type, type];
    //     }
    //     else if (ast.node == "apply") {
    //         const t1 = this.check(ast.exp1);
    //         const t2 = this.check(ast.exp2);
    //         if (Array.isArray(t1)) {
    //             if (
    //                 Array.isArray(t1[0]) &&
    //                 Array.isArray(t2) &&
    //                 arrayEquality(t1[0], t2)
    //             ) return t1[1];
    //             else if (t1[0] == t2) return t1[1];
    //             else typeMismatch(t1[0],t2)
    //         }
    //         nonFunction(t1);
    //     }
    //     else genericError("Unrecognizable ast node");
    // }

    prove(ast) {
        return printType(this.check(ast))
    }
}

module.exports = TypeChecker;