const Parser = require("./parser");
const TypeChecker = require("./type");
const parser = new Parser();
const check = new TypeChecker();

const ops = ["ADD", "SUB", "DIV", "MUL", "LBR", "AND", "OR", "GT", "LT", "EQ", "NEG", "NOT"];

const sym = {
    "ADD": "+",
    "MUL": "*",
    "SUB": "-",
    "DIV": "/",
    "AND": "&&",
    "OR": "||",
    "GT": ">",
    "LT": "<",
    "NOT": "!",
    "NEG": "-",
    "EQ": "==="
};

function transform(ast) {
    if(ast.node == "var") return ast.name;
    else if(ast.node == "literal") return ast.val;
    else if(ast.node == "lambda") {
        return `${ast.param}=>${transform(ast.body)}`;
    }
    else if(ast.node == "apply") {
        return `((${transform(ast.exp1)})(${transform(ast.exp2)}))`;
    }
    else if(ast.node == "condition") {
        return `((${transform(ast.cond)})?(${transform(ast.exp1)}):(${transform(ast.exp2)}))`;
    }
    else if(ops.includes(ast.node)) {
        return `((${transform(ast.l)})${sym[ast.node]}(${transform(ast.r)}))`;
    }
    else if(ast.node == "NEG") return `(-(${transform(ast.val)}))`;
}

function transpile(str) { 
    const ast = parser.parse(str);
    check.clear();
    check.prove(ast);
    return transform(ast);
}

module.exports = transpile;