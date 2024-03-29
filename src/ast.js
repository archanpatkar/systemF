const { sum } = require("styp");

const Expr = sum("Expr", {
    Var: ["name"],
    App: ["e1", "e2"],
    TApp: ["tl", "t"],
    Lit: ["type", "val"],
    TLam: ["param", "body"],
    Lam: ["param", "type", "body"],
    Cond: ["cond", "e1", "e2"],
    Let: ["name","e1","e2"],
    BinOp: ["op","l","r"],
    UnOp: ["op","v"]
});

module.exports = {
    Expr
};