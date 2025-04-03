package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.*;
import edu.utexas.cs.alr.parser.ExprBaseListener;
import edu.utexas.cs.alr.parser.ExprLexer;
import edu.utexas.cs.alr.parser.ExprParser;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.antlr.v4.runtime.tree.ParseTreeWalker;

import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.*;
import java.util.stream.Stream;

import static edu.utexas.cs.alr.ast.ExprFactory.*;
import static edu.utexas.cs.alr.util.ExprWalker.dfsWalk;

public class ExprUtils
{

    public static Expr toNNF(Expr expr)
    {
        ImplEquivTransformer tr1 = new ImplEquivTransformer();
        PushNegTransformer tr2 = new PushNegTransformer();

        dfsWalk(expr, tr1);
        Expr interExpr = tr1.newExpr(expr);
        dfsWalk(interExpr, tr2);

        return tr2.getTransformedExpr(interExpr);
    }

    public static Expr toCNF(Expr expr)
    {
        ExprCNFTransformer cnfTransformer = new ExprCNFTransformer();
        Expr nnfExpr = toNNF(expr);
        dfsWalk(nnfExpr, cnfTransformer);
        return cnfTransformer.getTransformedExpr(nnfExpr);
    }

    public static boolean isCNF(Expr expr) {
        if (expr.getKind() == Expr.ExprKind.AND) {
            AndExpr e = (AndExpr) expr;
            return isCNF(e.getLeft()) && isCNF(e.getRight());
        } else if (expr.getKind() == Expr.ExprKind.IMPL) {
            return false;
        } else if (expr.getKind() == Expr.ExprKind.EQUIV) {
            return false;
        } else if (expr.getKind() == Expr.ExprKind.NEG) {
            NegExpr e = (NegExpr) expr;
            return e.getExpr().getKind() == Expr.ExprKind.VAR;
        } else if (expr.getKind() == Expr.ExprKind.OR) {
            return isDisjunctionOfLiterals(expr);
        }
        return true;
    }

    public static boolean isDisjunctionOfLiterals(Expr expr) {
        if (expr.getKind() == Expr.ExprKind.OR) {
            OrExpr e = (OrExpr) expr;
            return isDisjunctionOfLiterals(e.getLeft()) && isDisjunctionOfLiterals(e.getRight());
        } else if (expr.getKind() == Expr.ExprKind.VAR) {
            return true;
        } else if (expr.getKind() == Expr.ExprKind.NEG) {
            NegExpr e = (NegExpr) expr;
            return e.getExpr().getKind() == Expr.ExprKind.VAR;
        }
        return false;
    }

    public static Expr toTseitin(Expr expr)
    {
        if (isCNF(expr))
            return expr;
        AuxVarCollectorListener auxVarCollectorListener = new AuxVarCollectorListener(getMaxVarID(expr) + 1);
        dfsWalk(expr, auxVarCollectorListener);

        Map<Expr, VarExpr> auxVarMap = auxVarCollectorListener.auxVarMap;
        TseitinClausesCollector tseitinClausesCollector = new TseitinClausesCollector(auxVarMap);
        dfsWalk(expr, tseitinClausesCollector);

        List<Expr> tseitinClauses = tseitinClausesCollector.tseitinClauses;
        return tseitinClauses.stream()
                             .reduce(auxVarMap.containsKey(expr) ? auxVarMap.get(expr) : expr,
                                     ExprFactory::mkAND);
    }

    public static Expr parseFrom(InputStream inStream) throws IOException
    {
        ExprLexer lexer = new ExprLexer(CharStreams.fromStream(inStream));
        BufferedTokenStream tokenStream = new BufferedTokenStream(lexer);
        ExprParser parser = new ExprParser(tokenStream);

        parser.addErrorListener(ThrowingErrorListener.INSTANCE);
        lexer.addErrorListener(ThrowingErrorListener.INSTANCE);

        ExprParser.ExprContext parseTree = parser.expr();
        ASTListener astListener = new ASTListener();
        ParseTreeWalker.DEFAULT.walk(astListener, parseTree);

        return astListener.pendingExpr.pop();
    }

    public static Expr parseFromDimcas(InputStream inStream)
    {
        Set<Expr> clauses = new HashSet<>();
        Scanner input = new Scanner(inStream);

        while(input.hasNextLine())
        {
            String l = input.nextLine();
            if (!l.startsWith("p cnf "))
            {
                clauses.add(Stream.of(l.split(" "))
                                  .map(Long::parseLong)
                                  .filter(lit -> !lit.equals(0L))
                                  .map(lit -> lit > 0 ? mkVAR(lit) : mkNEG(mkVAR(-lit)))
                                  .reduce(ExprFactory::mkOR).get());
            }
        }

        return clauses.stream()
                      .reduce(ExprFactory::mkAND)
                      .get();
    }

    public static void printDimcas(Expr expr, PrintStream out)
    {
        Set<Set<Long>> clauses = new HashSet<>();
        Set<Long> vars = new HashSet<>();

        Stack<Expr> s = new Stack<>();
        s.push(expr);

        while (!s.isEmpty())
        {
            Expr e = s.pop();

            if (!canBeCNF(e))
                throw new RuntimeException("Expr is not in CNF.");

            switch (e.getKind())
            {
                case AND:
                    AndExpr andExpr = (AndExpr) e;
                    s.push(andExpr.getLeft());
                    s.push(andExpr.getRight());
                    break;
                case NEG:
                    if (!isLiteral(e))
                        throw new RuntimeException("Expr is not in CNF.");

                    VarExpr childVarExpr = (VarExpr) ((NegExpr) e).getExpr();

                    clauses.add(Collections.singleton(-childVarExpr.getId()));
                    vars.add(childVarExpr.getId());
                    break;
                case VAR:
                    VarExpr varExpr = (VarExpr) e;
                    clauses.add(Collections.singleton(varExpr.getId()));
                    vars.add(varExpr.getId());
                    break;
                case OR:
                    clauses.add(getLiteralsForClause((OrExpr) e, vars));
                    break;
                default:
                    assert false;
            }
        }

        out.println("p cnf " + vars.size() + " " + clauses.size());

        clauses.forEach(c -> {
            c.forEach(l -> out.print(l + " "));
            out.println(0);
        });
    }

    public static boolean canBeCNF(Expr e)
    {
        Expr.ExprKind eKind = e.getKind();
        return eKind != Expr.ExprKind.EQUIV &&
               eKind != Expr.ExprKind.IMPL;
    }

    public static boolean isLiteral(Expr e)
    {
        Expr.ExprKind eKind = e.getKind();
        if (eKind == Expr.ExprKind.VAR)
            return true;

        if (eKind == Expr.ExprKind.NEG)
        {
            return ((NegExpr) e).getExpr().getKind() == Expr.ExprKind.VAR;
        }

        return false;
    }

    public static Set<Long> getLiteralsForClause(OrExpr orExpr, Set<Long> vars)
    {
        Set<Long> literals = new HashSet<>();
        Stack<Expr> s = new Stack<>();
        s.add(orExpr.getLeft());
        s.add(orExpr.getRight());

        while (!s.isEmpty())
        {
            Expr e = s.pop();

            if (e.getKind() != Expr.ExprKind.OR && !isLiteral(e))
                throw new RuntimeException("Expr is not in CNF");

            switch (e.getKind())
            {
                case OR:
                    OrExpr or = (OrExpr) e;
                    s.push(or.getLeft());
                    s.push(or.getRight());
                    break;
                case VAR:
                    long varId = ((VarExpr) e).getId();
                    literals.add(varId);
                    vars.add(varId);
                    break;
                case NEG:
                    NegExpr neg = (NegExpr) e;
                    long litId = -((VarExpr)neg.getExpr()).getId();
                    literals.add(litId);
                    vars.add(-litId);
                    break;
                default:
                    assert false;
            }
        }
        return literals;
    }

    private static long getMaxVarID(Expr e)
    {
        MaxIDListener maxIDListener = new MaxIDListener();
        dfsWalk(e, maxIDListener);
        return maxIDListener.maxID;
    }
}

class ASTListener extends ExprBaseListener
{
    Stack<Expr> pendingExpr = new Stack<>();

    @Override
    public void exitAtom(ExprParser.AtomContext ctx)
    {
        long id = Long.parseLong(ctx.VAR().toString().substring(1));
        VarExpr var = mkVAR(id);

        pendingExpr.push(var);
    }

    @Override
    public void exitLneg(ExprParser.LnegContext ctx)
    {
        Expr expr = pendingExpr.pop();
        NegExpr negExpr = mkNEG(expr);

        pendingExpr.push(negExpr);
    }

    @Override
    public void exitLand(ExprParser.LandContext ctx)
    {
        Expr right = pendingExpr.pop(), left = pendingExpr.pop();
        AndExpr andExpr = mkAND(left, right);

        pendingExpr.push(andExpr);
    }

    @Override
    public void exitLor(ExprParser.LorContext ctx)
    {
        Expr right = pendingExpr.pop(), left = pendingExpr.pop();
        OrExpr orExpr = mkOR(left, right);

        pendingExpr.push(orExpr);
    }

    @Override
    public void exitLimpl(ExprParser.LimplContext ctx)
    {
        Expr consequent = pendingExpr.pop(), antecedent = pendingExpr.pop();
        ImplExpr implExpr = mkIMPL(antecedent, consequent);

        pendingExpr.push(implExpr);
    }

    @Override
    public void exitLequiv(ExprParser.LequivContext ctx)
    {
        Expr right = pendingExpr.pop(), left = pendingExpr.pop();
        EquivExpr equivExpr = mkEQUIV(left, right);

        pendingExpr.push(equivExpr);
    }
}

class ThrowingErrorListener extends BaseErrorListener
{

    public static final ThrowingErrorListener INSTANCE = new ThrowingErrorListener();

    @Override
    public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine, String msg, RecognitionException e)
            throws ParseCancellationException
    {
        throw new ParseCancellationException("line " + line + ":" + charPositionInLine + " " + msg);
    }
}

class ImplEquivTransformer extends ExprBaseTransformASTListener
{
    @Override
    public void exitIMPL(ImplExpr e)
    {
        replMap.put(e, mkOR(mkNEG(newExpr(e.getAntecedent())),
                            newExpr(e.getConsequent())));
    }

    @Override
    public void exitEQUIV(EquivExpr e)
    {
        Expr newLeft = newExpr(e.getLeft());
        Expr newRight = newExpr(e.getRight());
        replMap.put(e, mkAND(mkOR(mkNEG(newExpr(newLeft)), newRight),
                             mkOR(mkNEG(newExpr(newRight)), newLeft)));
    }
}

class PushNegTransformer extends ExprBaseTransformASTListener
{
    Map<Expr, Expr> negReplMap = new HashMap<>();

    Stack<Boolean> inNeg = new Stack<>();

    @Override
    protected Expr newExpr(Expr e)
    {
        assert !isInNeg() || negReplMap.containsKey(e);
        return isInNeg() ? negReplMap.get(e) : super.newExpr(e);
    }

    private boolean isInNeg()
    {
        return !inNeg.isEmpty() && inNeg.peek();
    }

    @Override
    public void exitVAR(VarExpr e)
    {
        if (isInNeg())
        {
            negReplMap.put(e, mkNEG(e));
        }
        else super.exitVAR(e);
    }

    @Override
    public boolean enterNEG(NegExpr e)
    {
        inNeg.push(!isInNeg());
        return true;
    }

    @Override
    public void exitNEG(NegExpr e)
    {
        Expr newExpr = newExpr(e.getExpr());

        if (isInNeg())
            replMap.put(e, newExpr);
        else
            negReplMap.put(e, newExpr);

        inNeg.pop();
    }

    @Override
    public void exitOR(OrExpr e)
    {
        Expr newLeft = newExpr(e.getLeft());
        Expr newRight = newExpr(e.getRight());

        if (isInNeg())
            negReplMap.put(e, mkAND(newLeft, newRight));
        else
            replMap.put(e, mkOR(newLeft, newRight));
    }

    @Override
    public void exitAND(AndExpr e)
    {
        Expr newLeft = newExpr(e.getLeft());
        Expr newRight = newExpr(e.getRight());

        if (isInNeg())
            negReplMap.put(e, mkOR(newLeft, newRight));
        else
            replMap.put(e, mkAND(newLeft, newRight));
    }

    @Override
    public void exitIMPL(ImplExpr e)
    {
        throw new IllegalStateException("Formula needs to be transformed by ImplEquivTransformer first");
    }

    @Override
    public void exitEQUIV(EquivExpr e)
    {
        throw new IllegalStateException("Formula needs to be transformed by ImplEquivTransformer first");
    }
}

class ExprCNFTransformer extends ExprBaseTransformASTListener
{
    @Override
    public boolean enterNEG(NegExpr e)
    {
        if (e.getExpr().getKind() != Expr.ExprKind.VAR)
            throw new IllegalStateException("Expr is not in NNF");
        return super.enterNEG(e);
    }

    @Override
    public boolean enterIMPL(ImplExpr e)
    {
        throw new IllegalStateException("Expr is not in NNF");
    }

    @Override
    public boolean enterEQUIV(EquivExpr e)
    {
        throw new IllegalStateException("Expr is not in NNF");
    }

    @Override
    public void exitOR(OrExpr e)
    {
        Expr left = e.getLeft();
        Expr right = e.getRight();

        Expr newLeft = newExpr(left),
             newRight = newExpr(right);

        if (newLeft.getKind() == Expr.ExprKind.AND || newRight.getKind() == Expr.ExprKind.AND)
        {
            Set<Expr> leftClauses = clausesOf(newLeft),
                      rightClauses = clausesOf(newRight);

            List<Expr> newClauses = new ArrayList<>();
            for (Expr cl1 : leftClauses)
                for (Expr cl2 : rightClauses)
                    newClauses.add(mkOR(cl1, cl2));

            Expr newExpr = newClauses.subList(1, newClauses.size())
                                     .stream()
                                     .reduce(newClauses.get(0), ExprFactory::mkAND);

            replMap.put(e, newExpr);
        }
        else
        {
            super.exitOR(e);
        }
    }

    private Set<Expr> clausesOf(Expr e)
    {
        ClausesCollector clausesCollector = new ClausesCollector();
        dfsWalk(e, clausesCollector);
        return clausesCollector.clauses;
    }
}

class ClausesCollector extends ExprBaseASTListener
{
    Set<Expr> clauses = new HashSet<>();

    @Override
    public void enterVAR(VarExpr e)
    {
        clauses.add(e);
    }

    @Override
    public boolean enterNEG(NegExpr e)
    {
        clauses.add(e);
        return false;
    }

    @Override
    public boolean enterOR(OrExpr e)
    {
        clauses.add(e);
        return false;
    }
}

class MaxIDListener extends ExprBaseASTListener
{
    long maxID = 0;

    @Override
    public void exitVAR(VarExpr e)
    {
        maxID = Long.max(maxID, e.getId());
    }
}

class AuxVarCollectorListener extends ExprBaseASTListener
{
    Map<Expr, VarExpr> auxVarMap = new HashMap<>();

    long currId;

    public AuxVarCollectorListener(long startId)
    {
        this.currId = startId;
    }

    @Override
    public void exitNEG(NegExpr e)
    {
        if (!ExprUtils.isLiteral(e) && !auxVarMap.containsKey(e))
            auxVarMap.put(e, mkVAR(currId++));
    }

    @Override
    public void exitOR(OrExpr e)
    {
        if (!auxVarMap.containsKey(e))
            auxVarMap.put(e, mkVAR(currId++));
    }

    @Override
    public void exitAND(AndExpr e)
    {
        if (!auxVarMap.containsKey(e))
            auxVarMap.put(e, mkVAR(currId++));
    }

    @Override
    public void exitIMPL(ImplExpr e)
    {
        if (!auxVarMap.containsKey(e))
            auxVarMap.put(e, mkVAR(currId++));
    }

    @Override
    public void exitEQUIV(EquivExpr e)
    {
        if (!auxVarMap.containsKey(e))
            auxVarMap.put(e, mkVAR(currId++));
    }
}

class TseitinClausesCollector extends ExprBaseASTListener
{
    Map<Expr, VarExpr> auxVarMap;

    List<Expr> tseitinClauses = new ArrayList<>();

    public TseitinClausesCollector(Map<Expr, VarExpr> auxVarMap)
    {
        this.auxVarMap = auxVarMap;
    }

    Expr getAuxVarOrExpr(Expr e)
    {
        return auxVarMap.containsKey(e) ? auxVarMap.get(e) : e;
    }

    @Override
    public void exitNEG(NegExpr e)
    {
        if (!ExprUtils.isLiteral(e))
        {
            tseitinClauses.add(ExprUtils.toCNF(mkEQUIV(getAuxVarOrExpr(e),
                                                       mkNEG(getAuxVarOrExpr(e.getExpr())))));
        }
    }

    @Override
    public void exitOR(OrExpr e)
    {
        tseitinClauses.add(ExprUtils.toCNF(mkEQUIV(getAuxVarOrExpr(e),
                                                   mkOR(getAuxVarOrExpr(e.getLeft()),
                                                        getAuxVarOrExpr(e.getRight())))));
    }

    @Override
    public void exitAND(AndExpr e)
    {
        tseitinClauses.add(ExprUtils.toCNF(mkEQUIV(getAuxVarOrExpr(e),
                                                   mkAND(getAuxVarOrExpr(e.getLeft()),
                                                         getAuxVarOrExpr(e.getRight())))));
    }

    @Override
    public void exitIMPL(ImplExpr e)
    {
        tseitinClauses.add(ExprUtils.toCNF(mkEQUIV(getAuxVarOrExpr(e),
                                                   mkIMPL(getAuxVarOrExpr(e.getAntecedent()),
                                                          getAuxVarOrExpr(e.getConsequent())))));
    }

    @Override
    public void exitEQUIV(EquivExpr e)
    {
        tseitinClauses.add(ExprUtils.toCNF(mkEQUIV(getAuxVarOrExpr(e),
                                                   mkEQUIV(getAuxVarOrExpr(e.getLeft()),
                                                           getAuxVarOrExpr(e.getRight())))));
    }
}