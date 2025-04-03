//
// Program Name:	SATDriver.java
// Date Last Modified:	02/09/2025
// Last Modified By:    Lauren Escobedo
//
// Program Description: Programming assignment 1 for ALR
//

package edu.utexas.cs.alr;

import edu.utexas.cs.alr.ast.Expr;
import edu.utexas.cs.alr.util.ExprUtils;
import edu.utexas.cs.alr.util.SatUtil;

import org.antlr.v4.runtime.misc.ParseCancellationException;

import java.io.IOException;

public class SATDriver
{
    public static void main(String[] args) throws Exception
    {
        try
        {
            Expr e = ExprUtils.parseFrom(System.in);
            // Tseitin's Transformation
            Expr cnfExpr = ExprUtils.toTseitin(e);
			// System.out.println(cnfExpr);
            System.out.println(SatUtil.checkSAT(cnfExpr) ? "SAT" : "UNSAT");
        }
        catch (IOException ex)
        {
            System.err.println(ex.getMessage());
            ex.printStackTrace();
            System.exit(1);
        }
        catch (ParseCancellationException ex)
        {
            ex.printStackTrace();
            System.exit(1);
        }
    }
}
