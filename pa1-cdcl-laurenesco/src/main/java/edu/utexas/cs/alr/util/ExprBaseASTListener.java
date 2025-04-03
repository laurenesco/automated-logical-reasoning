package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.*;

public class ExprBaseASTListener implements ExprASTListener
{
    @Override
    public void enterVAR(VarExpr e)
    {

    }

    @Override
    public void exitVAR(VarExpr e)
    {

    }

    @Override
    public boolean enterNEG(NegExpr e)
    {
        return true;
    }

    @Override
    public void exitNEG(NegExpr e)
    {

    }

    @Override
    public boolean enterOR(OrExpr e)
    {
        return true;
    }

    @Override
    public void exitOR(OrExpr e)
    {

    }

    @Override
    public boolean enterAND(AndExpr e)
    {
        return true;
    }

    @Override
    public void exitAND(AndExpr e)
    {

    }

    @Override
    public boolean enterIMPL(ImplExpr e)
    {
        return true;
    }

    @Override
    public void exitIMPL(ImplExpr e)
    {

    }

    @Override
    public boolean enterEQUIV(EquivExpr e)
    {
        return true;
    }

    @Override
    public void exitEQUIV(EquivExpr e)
    {

    }
}
