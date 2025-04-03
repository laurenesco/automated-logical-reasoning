//
// Program Name:	SatUtil.java
// Date Last Modified:	02/09/2025
// Last Modfied By:	Lauren Escobedo
//
// Program Description: SAT solver
//

package edu.utexas.cs.alr.util;

import edu.utexas.cs.alr.ast.Expr;

import java.util.*;

///////////////////////
// SAT SOLVER CLASS
///////////////////////

public class SatUtil {

	public static int literals = 0;
	public static Clause lastConflictClause;
	private static Map<String, Boolean> decisionMap = new HashMap<>();

	// SAT solver method
    public static boolean checkSAT(Object f) {
		ImplicationGraph graph = new ImplicationGraph();
		int decisionLevel = 0;
		Formula formula = parseCNF(f.toString());
		AssignmentManager am = new AssignmentManager();
		Set<String> allVars = extractAllVariables(formula);

		while (true) {
			// Perform BCP
			boolean conflict = BCP(formula, am, graph, decisionLevel);
			if (conflict) {
				// Return UNSAT if conflict at root node
				if (decisionLevel == 0) {
					return false;
				}

				// Otherwise analyze conflict
				ConflictData conflictData = analyzeConflict(formula, am, graph, decisionLevel);
				formula.addClause(conflictData.learnedClause);
				am.backtrack(conflictData.backjumpLevel);
				decisionLevel = conflictData.backjumpLevel;
				graph.backtrack(conflictData.backjumpLevel);
			} else if (am.allAssigned(allVars)) {
				// Return SAT if all variables assigned
				return true;
			} else {
				String nextVar = pickNextVar(allVars, am);
				decisionLevel++;
				boolean value = decideValue(nextVar);
				am.assign(nextVar, value, decisionLevel, null);
				graph.addNode(new IGNode(nextVar, value, decisionLevel, null));
			}
		}
	}

	// ---------------- CDCL Related Functions Below  ---------------- //

	// Performs unit propagation, returns true if conflict
	private static boolean BCP(Formula formula, AssignmentManager am, ImplicationGraph graph, int decisionLevel) {
		boolean changed = true;
		// Loop until no new propagation is possible.
		while (changed) {
			changed = false;
			// Iterate over each clause.
			for (Clause clause : formula.clauses) {
				boolean satisfied = false;
				int unassignedCount = 0;
				Literal unitCandidate = null;
				// Check each literal in the clause.
				for (Literal lit : clause.literals) {
					Boolean assign = am.getAssignment(lit.name);
					if (assign != null) {
						// Evaluate the literal’s truth value.
						boolean litVal = lit.neg ? !assign : assign;
						if (litVal) {
							satisfied = true;
							break; // Clause is satisfied.
						}
					} else {
						unassignedCount++;
						unitCandidate = lit;
					}
				}
				// If clause is not satisfied:
				if (!satisfied) {
					if (unassignedCount == 0) {
						// All literals false => conflict.
						lastConflictClause = clause;
						return true;
					} else if (unassignedCount == 1) {
						// Exactly one literal is unassigned => unit clause.
						boolean valueToAssign = unitCandidate.neg ? false : true;
						if (!am.isAssigned(unitCandidate.name)) {
							am.assign(unitCandidate.name, valueToAssign, decisionLevel, clause);
							graph.addNode(new IGNode(unitCandidate.name, valueToAssign, decisionLevel, clause));
							changed = true; // New assignment may trigger further propagation.
						}
					}
				}
			}
		}
		return false;
	}

	private static ConflictData analyzeConflict(Formula formula, AssignmentManager am, ImplicationGraph graph, int decisionLevel) {
	 	// Use the conflict clause produced by BCP.
		if (lastConflictClause == null) {
			return new ConflictData(new Clause(Collections.emptyList()), 0);
		}
		Clause learnedClause = lastConflictClause;
		lastConflictClause = null;

		// Repeat resolution until there is exactly one literal from the current decision level.
		while (countLevelLiterals(learnedClause, am, decisionLevel) > 1) {
			// Pick a literal in learnedClause assigned at the current decision level.
			Literal pivot = pickLiteralFromClause(learnedClause, am, decisionLevel);
			if (pivot == null) break;

			// Locate the implication graph node for this literal.
			IGNode pivotNode = graph.findNode(pivot.name);
			if (pivotNode == null || pivotNode.leadingClause == null) {
				break;
			}
			// Convert the stored leadingClause (a string) into a Clause object.
			Clause antecedent = pivotNode.leadingClause;
			// Resolve the current learned clause with the antecedent on pivot.
			learnedClause = resolveClauses(learnedClause, antecedent, pivot);
		}

		// Determine the new backjump level: the maximum decision level among
		// literals in learnedClause except the one at the current decision level.
		int newBackjumpLevel = 0;
		for (Literal lit : learnedClause.literals) {
			int lvl = getDecisionLevelForLiteral(am, lit);
			if (lvl != decisionLevel && lvl > newBackjumpLevel) {
				newBackjumpLevel = lvl;
			}
		}
		return new ConflictData(learnedClause, newBackjumpLevel);
	}

	// Returns the count of literals in the clause assigned at decisionLevel.
	private static int countLevelLiterals(Clause clause, AssignmentManager am, int decisionLevel) {
		int count = 0;
		for (Literal lit : clause.literals) {
			if (getDecisionLevelForLiteral(am, lit) == decisionLevel) {
				count++;
			}
		}
		return count;
	}

	// Returns a literal from the clause assigned at decisionLevel.
	private static Literal pickLiteralFromClause(Clause clause, AssignmentManager am, int decisionLevel) {
		for (Literal lit : clause.literals) {
			if (getDecisionLevelForLiteral(am, lit) == decisionLevel) {
				return lit;
			}
		}
		return null;
	}

	// Resolves two clauses c1 and c2 on the pivot literal.
	// The resolution is: (c1 \ {pivot}) ∪ (c2 \ {~pivot}).
	private static Clause resolveClauses(Clause c1, Clause c2, Literal pivot) {
		Set<Literal> resolved = new HashSet<>();
		for (Literal lit : c1.literals) {
			// Exclude the pivot literal.
			if (!(lit.name.equals(pivot.name) && lit.neg == pivot.neg)) {
				resolved.add(lit);
			}
		}
		for (Literal lit : c2.literals) {
			// Exclude the complement of pivot.
			if (!(lit.name.equals(pivot.name) && lit.neg != pivot.neg)) {
				resolved.add(lit);
			}
		}
		return new Clause(new ArrayList<>(resolved));
	}

	// Returns the decision level for the literal by searching the assignment manager's decision stack.
	private static int getDecisionLevelForLiteral(AssignmentManager am, Literal lit) {
		// Assume am.getDecisionStack() returns a Collection<AssignmentManager.Decision>.
		for (AssignmentManager.Decision d : am.getDecisionStack()) {
			if (d.variable.equals(lit.name)) {
				return d.level;
			}
		}
		return 0; // default (should not happen for assigned literals)
	}

	// Pick next var. Naive for now, can implement heuristic
	private static String pickNextVar(Set<String> allVars, AssignmentManager am) {
		for (String var : allVars) {
			if (!am.isAssigned(var)) {

				return var;
			}
		}
		return null;
	}

	// Pick assignment. Naive for now, can implement heuristic
	private static boolean decideValue(String var) {
		boolean decision = !decisionMap.getOrDefault(var, false);
		decisionMap.put(var, decision);
		return decision;
	}

	private static Set<String> extractAllVariables(Formula formula) {
		Set<String> vars = new HashSet<>();

		for (Clause clause : formula.clauses) {
			for (Literal lit : clause.literals) {
				vars.add(lit.name);
			}
		}

		return vars;
	}

	// ----------------- CNF Input Parsing Functions Below ------------------//

	// Parse the raw CNF input and return a Formula object
	private static Formula parseCNF(String input) {
		Formula formula = new Formula();

		// Tokenize the string
		List<String> tokens = tokenize(input);

		// Create a nested list of clauses based on token list
		Object nestedList = parseTokens(tokens);

		// Process the expressions and create respective objects
		processClauses(nestedList, formula);

		return formula;
	}

	// Break the raw CNF input into tokens (e.g. "(", ")", "and", "or", "not", and literals
	private static List<String> tokenize(String input) {
		input = input.replace("(", " ( ").replace(")", " ) ");
		List<String> tokens = new ArrayList<>(Arrays.asList(input.trim().split("\\s+")));
		return tokens;
	}


	// Returns a list of clauses
	private static Object parseTokens(List<String> tokens) {
		// Create a nested list of clauses
		String token = tokens.remove(0);
		if (token.equals("(")) {
			// New clause
			List<Object> list = new ArrayList<>();
			while (!tokens.get(0).equals(")")) {
				list.add(parseTokens(tokens)); // Call recursively
			}
			tokens.remove(0); // Discard closing parenthesis
			return list;
		}
		// Unit clause case
		return token;
	}

	// Build all the respective objects
	private static void processClauses(Object nestedList, Formula formula) {
		if (nestedList instanceof String) {
			// Case of unit clause
			Literal lit = new Literal(SatUtil.literals, (String) nestedList, false);
			SatUtil.literals ++;

			Clause clause = new Clause(Collections.singletonList(lit));
			formula.addClause(clause);

		} else if (nestedList instanceof List) {
			// Case of list of clauses
			List<?> nestedListList = (List<?>) nestedList;
			if (nestedListList.isEmpty()) {
				return;
			}
			String operator = nestedListList.get(0).toString();

			if (operator.equals("and")) {
				// Process subexpressions
				for (int i = 1; i < nestedListList.size(); i++) {
					processClauses(nestedListList.get(i), formula); // Call recursively
				}
			} else if (operator.equals("or")) {
				// Build clause object
				List<Literal> lits = new ArrayList<>();
				for (int i = 1; i < nestedListList.size(); i++) {
					Object sub = nestedListList.get(i);
					if (sub instanceof List) {
						List<String> subList = (List<String>) sub;
						if (!subList.isEmpty() && subList.get(0).equals("not")) {
							lits.add(new Literal(SatUtil.literals, subList.get(1).toString(), true));
							SatUtil.literals++;
						} else {
							lits.add(new Literal(SatUtil.literals, sub.toString(), false));
							SatUtil.literals++;
						}
					} else {
						lits.add(new Literal(SatUtil.literals, sub.toString(), false));
						SatUtil.literals++;
					}
				}
				formula.addClause(new Clause(lits));
			} else if (operator.equals("not")) {
				// Negated literal
				Literal lit = new Literal(SatUtil.literals, nestedListList.get(1).toString(), true);
				SatUtil.literals++;
				formula.addClause(new Clause(Collections.singletonList(lit)));
			} else {
				// Literal
				Literal lit = new Literal(SatUtil.literals, operator, false);
				SatUtil.literals++;
				formula.addClause(new Clause(Collections.singletonList(lit)));
			}
		}
	}
}

/////////////////////////////
// IMPLICATION GRAPH CLASS
/////////////////////////////

// The Implication Graph
class ImplicationGraph {
	// Store all nodes
	List<IGNode> nodes = new ArrayList<>();

	public void addNode(IGNode node) { nodes.add(node); }

	public IGNode findNode(String literal) {
		for (IGNode node : nodes) {
			if (node.literal.equals(literal)) {
				return node;
			}
		}
		return null;
	}

	public void backtrack(int level) {
		Iterator<IGNode> i = nodes.iterator();

		while (i.hasNext()) {
			IGNode n = i.next();
			if (n.level > level) {
				i.remove();
			}
		}
	}

}

////////////////////////////////////
// IMPLICATION GRAPH NODE CLASS
////////////////////////////////////

// Implication graph nodes
class IGNode {
	String literal; 		// Which literal was assigned
	boolean assignment;		// What was the assignment
	int level; 				// What decision level was the assignment made
	Clause leadingClause;	// Clause on incoming edge (null if decision)
	List<IGNode> children;	// Nodes that were implied by this assignment

	// Constructor
	public IGNode(String l, boolean a, int lvl, Clause c) {
		this.literal = l;
		this.assignment = a;
		this.level = lvl;
		this.leadingClause = c;
		this.children = new ArrayList<>();
	}

	public void addChild(IGNode child) {
		children.add(child);
	}

}

///////////////////
// FORMULA CLASS
///////////////////

class Formula {
	List<Clause> clauses;		// What clauses compose the formula

	public Formula() {
		clauses = new ArrayList<Clause>();
	}

	public void addClause(Clause c) {
		clauses.add(c);
	}

}

///////////////////
// CLAUSE CLASS
///////////////////

class Clause {
	int id;						// Store an ID for the clause
	List<Literal> literals;		// Store the literals
	boolean unit;				// Is it a unit clause

	public Clause (List<Literal> l) {
		literals = l;

		if (l.isEmpty()) {
			unit = false;
		} else if (l.size() == 1) {
			// Unit clause
			unit = true;
		} else {
			unit = false;
		}
	}
}

///////////////////
// LITERAL CLASS
///////////////////

class Literal {
	int id;			// Store an ID for the literal
	String name;	// What is the display name for the literal
	boolean neg;	// Is it a negation

	public Literal(int i, String n, boolean negation) {
		this.id = i;
		this.name = n;
		this.neg = negation;
	}

	@Override
	public boolean equals(Object o) {
		if (this == o) return true;
		if (!(o instanceof Literal)) return false;
		Literal other = (Literal) o;
		return neg == other.neg && name.equals(other.name);
	}

	@Override
	public int hashCode() {
		return Objects.hash(name, neg);
	}
}

/////////////////////////
// ASSIGNMENT MANAGER
/////////////////////////

class AssignmentManager {
	private Map<String, Boolean> assignments = new HashMap<>();
	private Stack<Decision> decisionStack = new Stack<>();

	// Create a new assignment
	public void assign(String lit, boolean val, int lvl, Clause impliedBy) {
		assignments.put(lit, val);
		decisionStack.push(new Decision(lit, val, lvl, impliedBy));
	}

	// Check if variable is assigned
	public boolean isAssigned(String var) {
		return assignments.containsKey(var);
	}

	// Get current assignment (or null if unassigned)
	public Boolean getAssignment(String var) {
		return assignments.get(var);
	}

	// Check if all variables are assigned
	public boolean allAssigned(Set<String> allVariables) {
		return assignments.keySet().containsAll(allVariables);
	}

	public Collection<Decision> getDecisionStack() {
		return decisionStack; // or a copy if needed
	}

	// Backtrack to given level, remove assignments above that level
	public void backtrack(int targetDecisionLevel) {
		while (!decisionStack.isEmpty() && decisionStack.peek().level >= targetDecisionLevel) {
			Decision d = decisionStack.pop();
			assignments.remove(d.variable);
		}
	}

	static class Decision {
		public final String variable;
		public final boolean value;
		public final int level;
		public final Clause impliedBy; // Null if BCP decision



		public Decision(String variable, boolean value, int level, Clause impliedBy) {
			this.variable = variable;
            this.value = value;
            this.level = level;
            this.impliedBy = impliedBy;
		}
	}

}

/////////////////////////
// CONFLICT DATA CLASS
/////////////////////////

class ConflictData {
	Clause learnedClause;
	int backjumpLevel;

	ConflictData(Clause learnedClause, int backjumpLevel) {
		this.learnedClause = learnedClause;
		this.backjumpLevel = backjumpLevel;
	}
}
