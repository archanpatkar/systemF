// Type checker
// Based on -
// https://www.cl.cam.ac.uk/teaching/1415/L28/lambda.pdf
// https://crypto.stanford.edu/~blynn/lambda/systemf.html

// Dep
const { equal } = require("saman");
const { sum, tagged } = require("saman");

// const ops = ["ADD", "SUB", "DIV", "MUL"]

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

// // Utils
// function arrayEquality(a1, a2) {
//     let isEqual = false;
//     for (let e1 of a1) {
//         for (let e2 of a2) {
//             if (Array.isArray(e1) && Array.isArray(e2)) arrayEquality(e1, e2);
//             else if (e1 == e2) isEqual = true;
//             else isEqual = false;
//         }
//     }
//     return isEqual;
// }
// const printType = (type) => Array.isArray(type) ? `(${printType(type[0])}->${printType(type[1])})` : type;

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
        this.env = {};
    }

    clear() {
        this.env = {};
    }

    addBinding(name, type) {
        this.env[name] = type
    }

    removeBinding(name) {
        delete this.env[name]
    }

    lookUp(name) {
        if (this.env[name]) return this.env[name]
        notInScope(name);
    }

    check(ast) {
        if (ast.node == "literal") return ast.type
        if (ast.node == "var") return this.lookUp(ast.name)
        if (ops.includes(ast.node)) {
            const t1 = this.check(ast.l)
            const t2 = this.check(ast.r)
            if (t1 != "int" || t2 != "int") notType("int","for operands");
            return t1;
        }
        if(ast.node == "NEG") {
            const t1 = this.check(ast.val);
            if (t1 != "int") notType("int","for using unary '-' op");
            return t1;
        }
        if (ast.node == "condition") {
            const cond = this.check(ast.cond)
            if (cond != "bool") notType("bool","for 'if' condition");
            const t1 = this.check(ast.exp1)
            const t2 = this.check(ast.exp2)
            if (t1 != t2) generic("Expected same type for both branches");
            return t1;
        }
        else if (ast.node == "lambda") {
            this.addBinding(ast.param, ast.type);
            const type = this.check(ast.body);
            this.removeBinding(ast.param);
            return [ast.type, type];
        }
        else if (ast.node == "apply") {
            const t1 = this.check(ast.exp1);
            const t2 = this.check(ast.exp2);
            if (Array.isArray(t1)) {
                if (
                    Array.isArray(t1[0]) &&
                    Array.isArray(t2) &&
                    arrayEquality(t1[0], t2)
                ) return t1[1];
                else if (t1[0] == t2) return t1[1];
                else typeMismatch(t1[0],t2)
            }
            nonFunction(t1);
        }
        else genericError("Unrecognizable ast node");
    }

    prove(ast) {
        return printType(this.check(ast))
    }
}

module.exports = TypeChecker;