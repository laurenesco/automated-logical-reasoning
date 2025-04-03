package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.*;

public interface ExprASTListener
{
    void enterVAR(VarExpr e);

    void exitVAR(VarExpr e);

    boolean enterNEG(NegExpr e);

    void exitNEG(NegExpr e);

    boolean enterOR(OrExpr e);

    void exitOR(OrExpr e);

    boolean enterAND(AndExpr e);

    void exitAND(AndExpr e);

    boolean enterIMPL(ImplExpr e);

    void exitIMPL(ImplExpr e);

    boolean enterEQUIV(EquivExpr e);

    void exitEQUIV(EquivExpr e);
}
