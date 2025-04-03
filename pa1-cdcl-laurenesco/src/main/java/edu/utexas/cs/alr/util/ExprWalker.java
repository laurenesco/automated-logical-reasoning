package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.*;

public class ExprWalker
{
    public static void dfsWalk(Expr e, ExprASTListener listener)
    {
        boolean visitChildren = true;
        switch (e.getKind())
        {
            case VAR:
                VarExpr varExpr = (VarExpr) e;
                listener.enterVAR(varExpr);
                listener.exitVAR(varExpr);
                break;
            case NEG:
                NegExpr negExpr = (NegExpr) e;

                visitChildren = listener.enterNEG(negExpr);

                if (visitChildren)
                    dfsWalk(negExpr.getExpr(), listener);

                listener.exitNEG(negExpr);
                break;
            case AND:
                AndExpr andExpr = (AndExpr) e;

                visitChildren = listener.enterAND(andExpr);

                if (visitChildren)
                {
                    dfsWalk(andExpr.getLeft(), listener);
                    dfsWalk(andExpr.getRight(), listener);
                }

                listener.exitAND(andExpr);
                break;
            case OR:
                OrExpr orExpr = (OrExpr) e;

                visitChildren = listener.enterOR(orExpr);

                if (visitChildren)
                {
                    dfsWalk(orExpr.getLeft(), listener);
                    dfsWalk(orExpr.getRight(), listener);
                }

                listener.exitOR(orExpr);
                break;
            case IMPL:
                ImplExpr implExpr = (ImplExpr) e;

                visitChildren = listener.enterIMPL(implExpr);

                if (visitChildren)
                {
                    dfsWalk(implExpr.getAntecedent(), listener);
                    dfsWalk(implExpr.getConsequent(), listener);
                }

                listener.exitIMPL(implExpr);
                break;
            case EQUIV:
                EquivExpr equivExpr = (EquivExpr) e;

                visitChildren = listener.enterEQUIV(equivExpr);

                if (visitChildren)
                {
                    dfsWalk(equivExpr.getLeft(), listener);
                    dfsWalk(equivExpr.getRight(), listener);
                }

                listener.exitEQUIV(equivExpr);
                break;
            default:
                assert false;
        }
    }
}
