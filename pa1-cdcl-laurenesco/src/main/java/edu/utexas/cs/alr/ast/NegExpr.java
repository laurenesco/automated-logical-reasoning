package edu.utexas.cs.alr.ast;

import java.util.Objects;

public class NegExpr extends Expr
{
    private final Expr expr;

    NegExpr(Expr expr)
    {
        if (!Objects.nonNull(expr))
            throw new IllegalArgumentException("expr cannot be null");

        this.expr = expr;
    }

    public Expr getExpr()
    {
        return expr;
    }

    @Override
    public ExprKind getKind()
    {
        return ExprKind.NEG;
    }

    @Override
    public boolean equals(Object o)
    {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        NegExpr negExpr = (NegExpr) o;
        return expr.equals(negExpr.expr);
    }

    @Override
    public int hashCode()
    {
        return Objects.hash(expr);
    }

    @Override
    protected void prettyPrint(StringBuilder b, String indent)
    {
        b.append("(not ");
        expr.prettyPrint(b, indent + "     ");
        b.append(")");
    }
}
