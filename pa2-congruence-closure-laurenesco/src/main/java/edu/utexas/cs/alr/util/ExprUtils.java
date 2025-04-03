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
import java.util.*;

import static edu.utexas.cs.alr.ast.ExprFactory.*;

public class ExprUtils
{
    public static void validate(Set<Expr> exprs) {
        Map<Long, Integer> func2arg = new HashMap<>();
        for (Expr e : exprs) {
            check(e, func2arg);
        }
    }

    private static void check(Expr e, Map<Long, Integer> func2argcnt) {
        if (e instanceof EqExpr) {
            Expr left = ((EqExpr) e).getLeft();
            Expr right = ((EqExpr) e).getRight();
            if (left instanceof FappExpr) {
                check(left, func2argcnt);
            }
            if (right instanceof FappExpr) {
                check(right, func2argcnt);
            }
        } else if (e instanceof NeqExpr) {
            Expr left = ((NeqExpr) e).getLeft();
            Expr right = ((NeqExpr) e).getRight();
            if (left instanceof FappExpr) {
                check(left, func2argcnt);
            }
            if (right instanceof FappExpr) {
                check(right, func2argcnt);
            }
        } else if (e instanceof FappExpr) {
            FappExpr fExpr = (FappExpr) e;
            Integer argCnt = func2argcnt.get(fExpr.getId());
            if (argCnt != null && argCnt != fExpr.getExprs().size()) {
                throw new IllegalStateException("Function argument mismatch: "
                        + "f"+fExpr.getId() + " " + argCnt
                        + " != " + fExpr.getExprs().size());
            }
            func2argcnt.put(fExpr.getId(), fExpr.getExprs().size());
            for (Expr arg : fExpr.getExprs()) {
                check(arg, func2argcnt);
            }
        }
    }


    public static boolean checkSAT(Set<Expr> exprs) {
		Map<Expr, TermNode> termMap = new HashMap<>();
		List<EqExpr> equalities = new ArrayList<>();
		List<NeqExpr> disequalities = new ArrayList<>();

		// Step 1: Separate equalities and disequalities
		for (Expr expr : exprs) {
			if (expr instanceof EqExpr) {
				equalities.add((EqExpr) expr);
			} else if (expr instanceof NeqExpr) {
				disequalities.add((NeqExpr) expr);
			}
		}

		// Step 2: Build DAG by creating nodes
		for (EqExpr eq : equalities) {
			build(eq.getLeft(), termMap);
			build(eq.getRight(), termMap);
		}
		for (NeqExpr neq : disequalities) {
			build(neq.getLeft(), termMap);
			build(neq.getRight(), termMap);
		}

		// Step 3: Process equalities
		for (EqExpr eq : equalities) {
			TermNode l = termMap.get(eq.getLeft());
			TermNode r = termMap.get(eq.getRight());
			l.union(r);
		}

		// Step 4: Check disequalities
		for (NeqExpr neq : disequalities) {
			TermNode l = termMap.get(neq.getLeft()).find();
			TermNode r = termMap.get(neq.getRight()).find();
			if (l == r) return false; // UNSAT
		}

		return true; // SAT
	}

	public static void build(Expr expr, Map<Expr, TermNode> termMap) {
		if (termMap.containsKey(expr)) return;

		if (expr instanceof FappExpr) {
			for (Expr sub : ((FappExpr) expr).getExprs()) {
				build(sub, termMap);
			}
		}

		TermNode node = new TermNode(expr);
		termMap.put(expr, node);

		if (expr instanceof FappExpr) {
			for (Expr sub : ((FappExpr) expr).getExprs()) {
				termMap.get(sub).find().parents.add(node);
			}
		}
	}

	// Same as checkSAT, but add injective union
	public static boolean checkSATInjective(Set<Expr> exprs) {
		Map<Expr, TermNode> termMap = new HashMap<>();
		List<EqExpr> equalities = new ArrayList<>();
		List<NeqExpr> disequalities = new ArrayList<>();

		// Separate
		for (Expr expr : exprs) {
			if (expr instanceof EqExpr) {
				equalities.add((EqExpr) expr);
			} else if (expr instanceof NeqExpr) {
				disequalities.add((NeqExpr) expr);
			}
		}

		// Build DAG
		for (EqExpr eq : equalities) {
			build(eq.getLeft(), termMap);
			build(eq.getRight(), termMap);
		}
		for (NeqExpr neq : disequalities) {
			build(neq.getLeft(), termMap);
			build(neq.getRight(), termMap);
		}

		// Union with injective logic
		for (EqExpr eq : equalities) {
			TermNode a = termMap.get(eq.getLeft());
			TermNode b = termMap.get(eq.getRight());
			injectiveMerge(a, b, termMap, new HashSet<>());
		}

		// Check disequalities
		for (NeqExpr neq : disequalities) {
			TermNode a = termMap.get(neq.getLeft()).find();
			TermNode b = termMap.get(neq.getRight()).find();
			if (a == b) return false;
		}

		return true;
	}

	private static void injectiveMerge(TermNode a, TermNode b, Map<Expr, TermNode> termMap, Set<String> visited) {
		TermNode ra = a.find();
		TermNode rb = b.find();
		if (ra == rb) return;

		// Avoid infinite loops from reprocessing the same pair
		String key = System.identityHashCode(ra) + "#" + System.identityHashCode(rb);
		if (!visited.add(key)) return;

		// Injective rule: if same function symbol, force args to be equal
		if (ra.expr instanceof FappExpr && rb.expr instanceof FappExpr) {
			FappExpr f1 = (FappExpr) ra.expr;
			FappExpr f2 = (FappExpr) rb.expr;
			if (f1.getId() == f2.getId() && f1.getExprs().size() == f2.getExprs().size()) {
				List<Expr> args1 = f1.getExprs();
				List<Expr> args2 = f2.getExprs();
				for (int i = 0; i < args1.size(); i++) {
					TermNode arg1 = termMap.get(args1.get(i));
					TermNode arg2 = termMap.get(args2.get(i));
					if (arg1 != null && arg2 != null && arg1.find() != arg2.find()) {
						injectiveMerge(arg1, arg2, termMap, visited);
					}
				}
			}
		}

		ra.union(rb);
	}

    public static Set<Expr> parseFrom(InputStream inStream) throws IOException
    {
        ExprLexer lexer = new ExprLexer(CharStreams.fromStream(inStream));
        BufferedTokenStream tokenStream = new BufferedTokenStream(lexer);
        ExprParser parser = new ExprParser(tokenStream);

        parser.addErrorListener(ThrowingErrorListener.INSTANCE);
        lexer.addErrorListener(ThrowingErrorListener.INSTANCE);

        ExprParser.FormulaContext parseTree = parser.formula();
        ASTListener astListener = new ASTListener();
        ParseTreeWalker.DEFAULT.walk(astListener, parseTree);
        validate(astListener.conjuncts);
        return astListener.conjuncts;
    }

}

class ASTListener extends ExprBaseListener
{
    Stack<Expr> pendingExpr = new Stack<>();
    Set<Expr> conjuncts = new HashSet<>();

    @Override
    public void exitObj(ExprParser.ObjContext ctx) {
        if (ctx.FUNC() != null) {
            ArgExpr args = mkArgs(new ArrayList<>());
            Expr arg = pendingExpr.pop();
            // check if it is a single argument
            if (!(arg instanceof ArgExpr)) {
                args.getExprs().add(arg);
            } else {
                args = (ArgExpr) arg;
            }
            long funcId = Long.parseLong(ctx.FUNC().toString().substring(1));
            FappExpr fapp = mkFAPP(funcId, args.getExprs());
            pendingExpr.push(fapp);
        } else if (ctx.VAR() != null) {
            long id = Long.parseLong(ctx.VAR().toString().substring(1));
            VarExpr var = mkVAR(id);
            pendingExpr.push(var);
        }
    }

    @Override
    public void exitObjlist(ExprParser.ObjlistContext ctx) {
        int i = ctx.children.size()-1;
        List<Expr> exprs = new ArrayList<>();
        while(i > 0) {
            Expr popped = pendingExpr.pop();
            exprs.add(popped);
            i--;
        }
        Collections.reverse(exprs);
        if (exprs.size() > 0) {
            ArgExpr arg = mkArgs(exprs);
            pendingExpr.push(arg);
        }
    }

    @Override
    public void exitLequals(ExprParser.LequalsContext ctx) {
        Expr right = pendingExpr.pop(), left = pendingExpr.pop();
        EqExpr eqExpr = mkEq(left, right);

        conjuncts.add(eqExpr);
    }

    @Override
    public void exitLnequals(ExprParser.LnequalsContext ctx) {
        Expr right = pendingExpr.pop(), left = pendingExpr.pop();
        NeqExpr neqExpr = mkNeq(left, right);

        conjuncts.add(neqExpr);
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


class TermNode {
    Expr expr;
    TermNode parentRep; // term rep
    Set<TermNode> parents; // parents (only need for reps)

    TermNode(Expr expr) {
        this.expr = expr;
        this.parentRep = this;
        this.parents = new HashSet<>();
    }

    TermNode find() {
        if (parentRep != this) {
            parentRep = parentRep.find();
        }
        return parentRep;
    }

    void union(TermNode other) {
        TermNode r1 = this.find();
        TermNode r2 = other.find();
        if (r1 != r2) {
            r2.parentRep = r1;
            r1.parents.addAll(r2.parents); // merge parents
        }
    }
}

