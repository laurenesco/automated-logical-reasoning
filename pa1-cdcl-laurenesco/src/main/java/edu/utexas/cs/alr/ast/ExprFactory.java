package edu.utexas.cs.alr.ast;

import java.util.concurrent.ConcurrentHashMap;

public class ExprFactory
{
    private static final ConcurrentHashMap<Expr, Expr> cache = new ConcurrentHashMap<>();

    public static VarExpr mkVAR(long id)
    {
        VarExpr v = new VarExpr(id);
        cache.putIfAbsent(v, v);
        return (VarExpr) cache.get(v);
    }

    public static NegExpr mkNEG(Expr e)
    {
        NegExpr neg = new NegExpr(e);
        cache.putIfAbsent(neg, neg);
        return (NegExpr) cache.get(neg);
    }

    public static AndExpr mkAND(Expr left, Expr right)
    {
        AndExpr and = new AndExpr(left, right);
        cache.putIfAbsent(and, and);
        return (AndExpr) cache.get(and);
    }

    public static OrExpr mkOR(Expr left, Expr right)
    {
        OrExpr or = new OrExpr(left, right);
        cache.putIfAbsent(or, or);
        return (OrExpr) cache.get(or);
    }

    public static ImplExpr mkIMPL(Expr antecedent, Expr consequent)
    {
        ImplExpr impl = new ImplExpr(antecedent, consequent);
        cache.putIfAbsent(impl, impl);
        return (ImplExpr) cache.get(impl);
    }

    public static EquivExpr mkEQUIV(Expr left, Expr right)
    {
        EquivExpr equiv = new EquivExpr(left, right);
        cache.putIfAbsent(equiv, equiv);
        return (EquivExpr) cache.get(equiv);
    }
}
