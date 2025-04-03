package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.*;

import java.util.HashMap;
import java.util.Map;

import static edu.utexas.cs.alr.ast.ExprFactory.*;

public class ExprBaseTransformASTListener extends ExprBaseASTListener
{
    Map<Expr, Expr> replMap = new HashMap<>();

    protected Expr newExpr(Expr e)
    {
        return replMap.getOrDefault(e, e);
    }

    @Override
    public void exitVAR(VarExpr e)
    {
        newExpr(e);
    }

    @Override
    public void exitNEG(NegExpr e)
    {
        Expr inExpr = e.getExpr();
        Expr newInExpr = newExpr(inExpr);

        if (newInExpr != inExpr)
        {
            replMap.put(e, mkNEG(newInExpr));
        }
    }

    @Override
    public void exitOR(OrExpr e)
    {
        Expr left = e.getLeft(),
             right = e.getRight();

        Expr newLeft = newExpr(left),
             newRight = newExpr(right);

        if ((left != newLeft) ||
            (right != newRight))
        {
            replMap.put(e, mkOR(newLeft, newRight));
        }
    }

    @Override
    public void exitAND(AndExpr e)
    {
        Expr left = e.getLeft(),
             right = e.getRight();

        Expr newLeft = newExpr(left),
                newRight = newExpr(right);

        if ((left != newLeft) ||
            (right != newRight))
        {
            replMap.put(e, mkAND(newLeft, newRight));
        }
    }

    @Override
    public void exitIMPL(ImplExpr e)
    {
        Expr antecedent = e.getAntecedent(),
             consequent = e.getConsequent();

        Expr newAntecedent = newExpr(antecedent),
             newConsequent = newExpr(consequent);

        if ((newAntecedent != antecedent) ||
            (newConsequent != consequent))
        {
            replMap.put(e, mkIMPL(newAntecedent, newConsequent));
        }
    }

    @Override
    public void exitEQUIV(EquivExpr e)
    {
        Expr left = e.getLeft(),
                right = e.getRight();

        Expr newLeft = newExpr(left),
                newRight = newExpr(right);

        if ((left != newLeft) ||
            (right != newRight))
        {
            replMap.put(e, mkEQUIV(newLeft, newRight));
        }
    }

    public Expr getTransformedExpr(Expr e)
    {
        return newExpr(e);
    }
}
