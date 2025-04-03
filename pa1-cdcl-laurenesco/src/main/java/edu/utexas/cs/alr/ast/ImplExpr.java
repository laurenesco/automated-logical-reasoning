package edu.utexas.cs.alr.ast;

import java.util.Objects;

public class ImplExpr extends Expr
{
    private final Expr antecedent;

    private final Expr consequent;

    ImplExpr(Expr antecedent, Expr consequent)
    {
        if (!Objects.nonNull(antecedent))
            throw new IllegalArgumentException("antecedent expr cannot be null");
        if (!Objects.nonNull(consequent))
            throw new IllegalArgumentException("consequent expr cannot be null");

        this.antecedent = antecedent;
        this.consequent = consequent;
    }

    public Expr getAntecedent()
    {
        return antecedent;
    }

    public Expr getConsequent()
    {
        return consequent;
    }

    @Override
    public ExprKind getKind()
    {
        return ExprKind.IMPL;
    }

    @Override
    public boolean equals(Object o)
    {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ImplExpr implExpr = (ImplExpr) o;
        return antecedent.equals(implExpr.antecedent) && consequent.equals(implExpr.consequent);
    }

    @Override
    public int hashCode()
    {
        return Objects.hash(antecedent, consequent);
    }

    @Override
    protected void prettyPrint(StringBuilder b, String indent)
    {
        b.append("(impl ");
        antecedent.prettyPrint(b, indent + "      ");
        b.append("\n").append(indent).append("      ");
        consequent.prettyPrint(b, indent + "      ");
        b.append(")");
    }
}
