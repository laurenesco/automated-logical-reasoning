package edu.utexas.cs.alr.ast;

import java.util.Objects;

public class EquivExpr extends Expr
{
    private final Expr leftExpr;

    private final Expr rightExpr;

    EquivExpr(Expr left, Expr right)
    {
        if (!Objects.nonNull(left))
            throw new IllegalArgumentException("Expr left cannot be null");
        if (!Objects.nonNull(right))
            throw new IllegalArgumentException("Expr right cannot be null");

        this.leftExpr = left;
        this.rightExpr = right;
    }

    public Expr getLeft()
    {
        return leftExpr;
    }

    public Expr getRight()
    {
        return rightExpr;
    }

    @Override
    public ExprKind getKind()
    {
        return ExprKind.EQUIV;
    }

    @Override
    public boolean equals(Object o)
    {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        EquivExpr equivExpr = (EquivExpr) o;
        return (leftExpr.equals(equivExpr.leftExpr) && rightExpr.equals(equivExpr.rightExpr));
    }

    @Override
    public int hashCode()
    {
        return Objects.hash(leftExpr, rightExpr);
    }

    @Override
    protected void prettyPrint(StringBuilder b, String indent)
    {
        b.append("(equiv ");
        leftExpr.prettyPrint(b, indent + "       ");
        b.append("\n").append(indent).append("       ");
        rightExpr.prettyPrint(b, indent + "       ");
        b.append(")");
    }
}
