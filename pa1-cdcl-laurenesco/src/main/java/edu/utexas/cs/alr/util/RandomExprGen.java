package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.Expr;
import edu.utexas.cs.alr.ast.VarExpr;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import static edu.utexas.cs.alr.ast.ExprFactory.*;

public class RandomExprGen
{
    private final long depth;

    private final Random rand = new Random();

    private final Set<VarExpr> vars = new HashSet<>();

    private long nextVarId = 1;

    public RandomExprGen(long depth)
    {
        this.depth = depth;
    }

    public Expr gen()
    {
        return genExpr(depth);
    }

    private VarExpr getVar()
    {
        if (!vars.isEmpty() && rand.nextBoolean())
        {
            VarExpr[] varsAsArray = vars.toArray(new VarExpr[0]);
            return varsAsArray[rand.nextInt(varsAsArray.length)];
        }
        else
        {
            VarExpr varExpr = mkVAR(nextVarId++);
            vars.add(varExpr);
            return varExpr;
        }
    }

    private Expr genExpr(long depth)
    {
        if (depth == 0)
        {
            return getVar();
        }
        else
        {
            Expr newExpr = null;
            switch (rand.nextInt(5))
            {
                case 0:
                {
                    Expr left = genExpr(depth - 1);
                    Expr right = rand.nextBoolean() ? genExpr(depth - 1) : mkNEG(left);

                    newExpr = mkAND(left, right);
                }
                    break;
                case 1:
                {
                    Expr left = genExpr(depth - 1);
                    Expr right = rand.nextBoolean() ? genExpr(depth - 1) : mkNEG(left);

                    newExpr = mkEQUIV(left, right);
                }
                    break;
                case 2:
                {
                    Expr antecedent = genExpr(depth - 1);
                    Expr consequent = genExpr(depth - 1);

                    newExpr = mkIMPL(antecedent, consequent);
                }
                    break;
                case 3:
                {
                    Expr e = genExpr(depth - 1);

                    newExpr = mkNEG(e);
                }
                    break;
                case 4:
                {
                    Expr left = genExpr(depth - 1);
                    Expr right = genExpr(depth - 1);

                    newExpr = mkOR(left, right);
                }
                    break;
                default:
                    assert false;
            }

            assert newExpr != null;

            return newExpr;
        }
    }

}
