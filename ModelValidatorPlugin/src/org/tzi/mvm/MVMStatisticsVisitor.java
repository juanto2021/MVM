package org.tzi.mvm;

import java.util.LinkedList;
import java.util.List;

import org.tzi.use.uml.ocl.expr.ExpAllInstances;
import org.tzi.use.uml.ocl.expr.ExpAny;
import org.tzi.use.uml.ocl.expr.ExpAsType;
import org.tzi.use.uml.ocl.expr.ExpAttrOp;
import org.tzi.use.uml.ocl.expr.ExpBagLiteral;
import org.tzi.use.uml.ocl.expr.ExpClosure;
import org.tzi.use.uml.ocl.expr.ExpCollect;
import org.tzi.use.uml.ocl.expr.ExpCollectNested;
import org.tzi.use.uml.ocl.expr.ExpConstBoolean;
import org.tzi.use.uml.ocl.expr.ExpConstEnum;
import org.tzi.use.uml.ocl.expr.ExpConstInteger;
import org.tzi.use.uml.ocl.expr.ExpConstReal;
import org.tzi.use.uml.ocl.expr.ExpConstString;
import org.tzi.use.uml.ocl.expr.ExpConstUnlimitedNatural;
import org.tzi.use.uml.ocl.expr.ExpEmptyCollection;
import org.tzi.use.uml.ocl.expr.ExpExists;
import org.tzi.use.uml.ocl.expr.ExpForAll;
import org.tzi.use.uml.ocl.expr.ExpIf;
import org.tzi.use.uml.ocl.expr.ExpInvalidException;
import org.tzi.use.uml.ocl.expr.ExpIsKindOf;
import org.tzi.use.uml.ocl.expr.ExpIsTypeOf;
import org.tzi.use.uml.ocl.expr.ExpIsUnique;
import org.tzi.use.uml.ocl.expr.ExpIterate;
import org.tzi.use.uml.ocl.expr.ExpLet;
import org.tzi.use.uml.ocl.expr.ExpNavigation;
import org.tzi.use.uml.ocl.expr.ExpNavigationClassifierSource;
import org.tzi.use.uml.ocl.expr.ExpObjAsSet;
import org.tzi.use.uml.ocl.expr.ExpObjOp;
import org.tzi.use.uml.ocl.expr.ExpObjRef;
import org.tzi.use.uml.ocl.expr.ExpObjectByUseId;
import org.tzi.use.uml.ocl.expr.ExpOclInState;
import org.tzi.use.uml.ocl.expr.ExpOne;
import org.tzi.use.uml.ocl.expr.ExpOrderedSetLiteral;
import org.tzi.use.uml.ocl.expr.ExpQuery;
import org.tzi.use.uml.ocl.expr.ExpRange;
import org.tzi.use.uml.ocl.expr.ExpReject;
import org.tzi.use.uml.ocl.expr.ExpSelect;
import org.tzi.use.uml.ocl.expr.ExpSelectByKind;
import org.tzi.use.uml.ocl.expr.ExpSelectByType;
import org.tzi.use.uml.ocl.expr.ExpSequenceLiteral;
import org.tzi.use.uml.ocl.expr.ExpSetLiteral;
import org.tzi.use.uml.ocl.expr.ExpSortedBy;
import org.tzi.use.uml.ocl.expr.ExpStdOp;
import org.tzi.use.uml.ocl.expr.ExpTupleLiteral;
import org.tzi.use.uml.ocl.expr.ExpTupleSelectOp;
import org.tzi.use.uml.ocl.expr.ExpUndefined;
import org.tzi.use.uml.ocl.expr.ExpVariable;
import org.tzi.use.uml.ocl.expr.Expression;
import org.tzi.use.uml.ocl.expr.ExpressionVisitor;
import org.tzi.use.uml.ocl.expr.ExpressionWithValue;
import org.tzi.use.uml.ocl.expr.VarDecl;
import org.tzi.use.uml.ocl.expr.VarDeclList;
import org.tzi.use.uml.ocl.type.Type;
import org.tzi.use.uml.ocl.type.TypeFactory;

public class MVMStatisticsVisitor implements ExpressionVisitor{
	
	private List<Expression> expression;
	
	public MVMStatisticsVisitor() {
		expression = new LinkedList<Expression>();
	}
	public List<Expression> getExpr() {
		return expression;
	}

	@Override
	public void visitAllInstances(ExpAllInstances exp) {
		System.out.println("visitAllInstances - exp ( " + exp + ")");
		
	}

	@Override
	public void visitAny(ExpAny exp) {
		System.out.println("visitAny - exp ( " + exp + ")");
		
	}

	@Override
	public void visitAsType(ExpAsType exp) {
		System.out.println("visitAsType - exp ( " + exp + ")");
		
	}

	@Override
	public void visitAttrOp(ExpAttrOp exp) {
		System.out.println("visitAttrOp - exp ( " + exp + ")");
		
	}

	@Override
	public void visitBagLiteral(ExpBagLiteral exp) {
		System.out.println("visitBagLiteral - exp ( " + exp + ")");
		
	}

	@Override
	public void visitCollect(ExpCollect exp) {
		System.out.println("visvisitCollectitIf - exp ( " + exp + ")");
		
	}

	@Override
	public void visitCollectNested(ExpCollectNested exp) {
		System.out.println("visitCollectNested - exp ( " + exp + ")");
		
	}

	@Override
	public void visitConstBoolean(ExpConstBoolean exp) {
		System.out.println("visitConstBoolean - exp ( " + exp + ")");
		
	}

	@Override
	public void visitConstEnum(ExpConstEnum exp) {
		System.out.println("visitConstEnum - exp ( " + exp + ")");
		
	}

	@Override
	public void visitConstInteger(ExpConstInteger exp) {
		System.out.println("visitConstInteger - exp ( " + exp + ")");
		
	}

	@Override
	public void visitConstReal(ExpConstReal exp) {
		System.out.println("visitConstReal - exp ( " + exp + ")");
		
	}

	@Override
	public void visitConstString(ExpConstString exp) {
		System.out.println("visitConstString - exp ( " + exp + ")");
		
	}

	@Override
	public void visitEmptyCollection(ExpEmptyCollection exp) {
		System.out.println("visitEmptyCollection - exp ( " + exp + ")");
		
	}

	@Override
	public void visitExists(ExpExists exp) {
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();	
		VarDeclList decl = exp.getVariableDeclarations();		
		System.out.println("visitExists - exp ( " + exp + ")");
		System.out.println("visitExists - query ( " + query + ")");	
		System.out.println("visitExists - range ( " + range + ")");	
		System.out.println("visitExists - decl ( " + decl.toString() + ")");			
		expression.add(query);
	}

	@Override
	public void visitForAll(ExpForAll exp) {
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();	
		VarDeclList decl = exp.getVariableDeclarations();		
		System.out.println("visitForAll - exp ( " + exp + ")");
		System.out.println("visitForAll - query ( " + query + ")");	
		System.out.println("visitForAll - range ( " + range + ")");	
		System.out.println("visitForAll - decl ( " + decl.toString() + ")");
		
		expression.add(query);	
	}

	@Override
	public void visitIf(ExpIf exp) {
		System.out.println("visitIf - exp ( " + exp + ")");
		
	}

	@Override
	public void visitIsKindOf(ExpIsKindOf exp) {
		System.out.println("visitIsKindOf - exp ( " + exp + ")");
		
	}

	@Override
	public void visitIsTypeOf(ExpIsTypeOf exp) {
		System.out.println("visitIsTypeOf - exp ( " + exp + ")");
		
	}

	@Override
	public void visitIsUnique(ExpIsUnique exp) {
		System.out.println("visitIsUnique - exp ( " + exp + ")");
		
	}

	@Override
	public void visitIterate(ExpIterate exp) {
		System.out.println("visitIterate - exp ( " + exp + ")");
		
	}

	@Override
	public void visitLet(ExpLet exp) {
		System.out.println("visitLet - exp ( " + exp + ")");
		
	}

	@Override
	public void visitNavigation(ExpNavigation exp) {
		System.out.println("visitNavigation - exp ( " + exp + ")");
		
	}

	@Override
	public void visitObjAsSet(ExpObjAsSet exp) {
		System.out.println("visitObjAsSet - exp ( " + exp + ")");
		
	}

	@Override
	public void visitObjOp(ExpObjOp exp) {
		System.out.println("visitObjOp - exp ( " + exp + ")");
		
	}

	@Override
	public void visitObjRef(ExpObjRef exp) {
		System.out.println("visitObjRef - exp ( " + exp + ")");
		
	}

	@Override
	public void visitOne(ExpOne exp) {
		System.out.println("visitOne - exp ( " + exp + ")");
		
	}

	@Override
	public void visitOrderedSetLiteral(ExpOrderedSetLiteral exp) {
		System.out.println("visitOrderedSetLiteral - exp ( " + exp + ")");
		
	}

	@Override
	public void visitQuery(ExpQuery exp) {
		System.out.println("visitQuery - exp ( " + exp + ")");
		
	}

	@Override
	public void visitReject(ExpReject exp) {
		System.out.println("visitReject - exp ( " + exp + ")");
		
	}

	@Override
	public void visitWithValue(ExpressionWithValue exp) {
		System.out.println("visitWithValue - exp ( " + exp + ")");
		
	}

	@Override
	public void visitSelect(ExpSelect exp) {
		System.out.println("visitSelect - exp ( " + exp + ")");
		
	}

	@Override
	public void visitSequenceLiteral(ExpSequenceLiteral exp) {
		System.out.println("visitSequenceLiteral - exp ( " + exp + ")");
		
	}

	@Override
	public void visitSetLiteral(ExpSetLiteral exp) {
		System.out.println("visitSetLiteral - exp ( " + exp + ")");
		
	}

	@Override
	public void visitSortedBy(ExpSortedBy exp) {
		System.out.println("visitSortedBy - exp ( " + exp + ")");
		
	}

	@Override
	public void visitStdOp(ExpStdOp exp) {
		System.out.println("visitStdOp - exp ( " + exp + ")");
		// Place-holder for operations returning a boolean value
		// Boolean: or, xor, and, not, implies
		// Collection operations: isEmpty, notEmpty, includes, excludes, includesAll, excludesAll
		// Relational: <=, >=, <, >, =, <>
		String opName = exp.opname();
		switch(opName) {
		case "or":
			expression(exp);
			break;	
		case "xor":
			mutateXorExp(exp); 
			break;
		case "and":
			mutateAndExp(exp);
			break;
		case "not":
			mutateNotExp(exp);
			break;	
		case "implies":
			mutateImpliesExp(exp);
			break;	
		case "=":
			// De momento no ponemos nada
			defaultStrengthening();
			break;	
		case "<=":
			mutateLessEqualExp(exp); 
			break;	
		case ">=":
			mutateGreaterEqualExp(exp);
			break;	
		case "<":
			mutateLessExp(exp);
			break;	
		case ">":
			mutateGreaterExp(exp);
			break;	
		case "<>":
			mutateNotEqualsExp(exp); 
			break;	
		case "isEmpty":
			mutateIsEmptyExp(exp);
			break;	
		case "notEmpty":
			mutateNotEmptyExp(exp);
			break;	
		case "includes":
			mutateIncludesExp(exp);
			break;	
		case "excludes":
			mutateExcludesExp(exp);
			break;	
		case "includesAll":
			mutateIncludesAllExp(exp);
			break;	
		case "excludesAll":
			mutateExcludesAllExp(exp);
			break;	
		default:
			wrongTypeError("unsupported operation type '" + opName + "'");
		}		
		
	}

	@Override
	public void visitTupleLiteral(ExpTupleLiteral exp) {
		System.out.println("visitTupleLiteral - exp ( " + exp + ")");
		
	}

	@Override
	public void visitTupleSelectOp(ExpTupleSelectOp exp) {
		System.out.println("visitTupleSelectOp - exp ( " + exp + ")");
		
	}

	@Override
	public void visitUndefined(ExpUndefined exp) {
		System.out.println("visitUndefined - exp ( " + exp + ")");
		
	}

	@Override
	public void visitVariable(ExpVariable exp) {
		System.out.println("visitVariable - exp ( " + exp + ")");
		
	}

	@Override
	public void visitClosure(ExpClosure exp) {
		System.out.println("visitClosure - exp ( " + exp + ")");
		
	}

	@Override
	public void visitOclInState(ExpOclInState exp) {
		System.out.println("visitOclInState - exp ( " + exp + ")");
		
	}

	@Override
	public void visitVarDeclList(VarDeclList varDeclList) {
		System.out.println("visitVarDeclList - varDeclList ( " + varDeclList + ")");
		
	}

	@Override
	public void visitVarDecl(VarDecl varDecl) {
		System.out.println("visitVarDecl - varDecl ( " + varDecl + ")");
		
	}

	@Override
	public void visitObjectByUseId(ExpObjectByUseId exp) {
		System.out.println("visitObjectByUseId - exp ( " + exp + ")");
		
	}

	@Override
	public void visitConstUnlimitedNatural(ExpConstUnlimitedNatural exp) {
		System.out.println("visitConstUnlimitedNatural - exp ( " + exp + ")");
		
	}

	@Override
	public void visitSelectByKind(ExpSelectByKind exp) {
		System.out.println("visitSelectByKind - exp ( " + exp + ")");
		
	}

	@Override
	public void visitExpSelectByType(ExpSelectByType exp) {
		System.out.println("visitExpSelectByType - exp ( " + exp + ")");
		
	}

	@Override
	public void visitRange(ExpRange exp) {
		System.out.println("visitRange - exp ( " + exp + ")");
		
	}

	@Override
	public void visitNavigationClassifierSource(ExpNavigationClassifierSource exp) {
		System.out.println("visitNavigationClassifierSource - exp ( " + exp + ")");
		
	}
	private void expression(ExpStdOp exp) {
		Expression[] args = exp.args();
		
		// Retrieve subexpressions
		// Sanity check: "or" is a binary expression
		assert(args.length == 2);
		Expression left  = args[0];
		Expression right = args[1];
		
		List<Expression> leftMutants  = strengthen(left);
		List<Expression> rightMutants = strengthen(right); 
		
		// Mutation 1: Strengthen the left subexpression
		for(Expression mutant: leftMutants) {
			Expression newArgs[] = {mutant, right};
			try {
				Expression mutant1 = ExpStdOp.create("or", newArgs);
				expression.add(mutant1);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
		 
		// Mutation 2: Strengthen the right subexpression
		for(Expression mutant: rightMutants) {
			Expression newArgs[] = {left, mutant};
			try {
				Expression mutant2 = ExpStdOp.create("or", newArgs);
				expression.add(mutant2);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
			
		// Mutation 3: Strengthen both subexpressions
		for(Expression mutantA: leftMutants) {
			for (Expression mutantB: rightMutants) {
				Expression newArgs[] = {mutantA, mutantB};
				try {
					Expression mutant3 = ExpStdOp.create("or", newArgs);
					expression.add(mutant3);
				} catch (ExpInvalidException e) {
					e.printStackTrace();
				}
			}
		}
			
		// Mutation 4: Replace the "or" with an "and"
		try {
			Expression mutant4 = ExpStdOp.create("and", args);
			expression.add(mutant4);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 5: Strengthen the left subexpression and replace with "and"
		for(Expression mutant: leftMutants) {
			Expression newArgs[] = {mutant, right};
			try {
				Expression mutant5 = ExpStdOp.create("and", newArgs);
				expression.add(mutant5);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
				
		// Mutation 6: Strengthen the right subexpression and replace with "and"
		for(Expression mutant: rightMutants) {
			Expression newArgs[] = {left, mutant};
			try {
				Expression mutant6 = ExpStdOp.create("and", newArgs);
				expression.add(mutant6);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
					
		// Mutation 7: Strengthen both subexpressions and replace with "and"
		for(Expression mutantA: leftMutants) {
			for (Expression mutantB: rightMutants) {
				Expression newArgs[] = {mutantA, mutantB};
				try {
					Expression mutant3 = ExpStdOp.create("or", newArgs);
					expression.add(mutant3);
				} catch (ExpInvalidException e) {
					e.printStackTrace();
				}
			}
		}
			
		// Mutation 8: Replace the "or" with an "xor"
		// We should not strengthen the arguments!
		try {
			Expression mutant8 = ExpStdOp.create("xor", args);
			expression.add(mutant8);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
				
		// Mutation 9: Replace the "or" expression by "false" 
		defaultStrengthening();
	}
	private static List<Expression> strengthen(Expression exp) {
		MVMStatisticsVisitor vis = new MVMStatisticsVisitor();
		System.out.println("RECURSIVIDAD - strengthen exp ( " + exp + ")");
		exp.processWithVisitor(vis);
		return vis.getExpr();
	}
	
	private void mutateOrExp(ExpStdOp exp) {
		Expression[] args = exp.args();
		
		// Retrieve subexpressions
		// Sanity check: "or" is a binary expression
		assert(args.length == 2);
		Expression left  = args[0];
		Expression right = args[1];
		
		List<Expression> leftMutants  = strengthen(left);
		List<Expression> rightMutants = strengthen(right); 
		
		// Mutation 1: Strengthen the left subexpression
		for(Expression mutant: leftMutants) {
			Expression newArgs[] = {mutant, right};
			try {
				Expression mutant1 = ExpStdOp.create("or", newArgs);
				expression.add(mutant1);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
		 
		// Mutation 2: Strengthen the right subexpression
		for(Expression mutant: rightMutants) {
			Expression newArgs[] = {left, mutant};
			try {
				Expression mutant2 = ExpStdOp.create("or", newArgs);
				expression.add(mutant2);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
			
		// Mutation 3: Strengthen both subexpressions
		for(Expression mutantA: leftMutants) {
			for (Expression mutantB: rightMutants) {
				Expression newArgs[] = {mutantA, mutantB};
				try {
					Expression mutant3 = ExpStdOp.create("or", newArgs);
					expression.add(mutant3);
				} catch (ExpInvalidException e) {
					e.printStackTrace();
				}
			}
		}
			
		// Mutation 4: Replace the "or" with an "and"
		try {
			Expression mutant4 = ExpStdOp.create("and", args);
			expression.add(mutant4);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 5: Strengthen the left subexpression and replace with "and"
		for(Expression mutant: leftMutants) {
			Expression newArgs[] = {mutant, right};
			try {
				Expression mutant5 = ExpStdOp.create("and", newArgs);
				expression.add(mutant5);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
				
		// Mutation 6: Strengthen the right subexpression and replace with "and"
		for(Expression mutant: rightMutants) {
			Expression newArgs[] = {left, mutant};
			try {
				Expression mutant6 = ExpStdOp.create("and", newArgs);
				expression.add(mutant6);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
					
		// Mutation 7: Strengthen both subexpressions and replace with "and"
		for(Expression mutantA: leftMutants) {
			for (Expression mutantB: rightMutants) {
				Expression newArgs[] = {mutantA, mutantB};
				try {
					Expression mutant3 = ExpStdOp.create("or", newArgs);
					expression.add(mutant3);
				} catch (ExpInvalidException e) {
					e.printStackTrace();
				}
			}
		}
			
		// Mutation 8: Replace the "or" with an "xor"
		// We should not strengthen the arguments!
		try {
			Expression mutant8 = ExpStdOp.create("xor", args);
			expression.add(mutant8);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
				
		// Mutation 9: Replace the "or" expression by "false" 
		defaultStrengthening();
	}
	
	private void mutateAndExp(ExpStdOp exp) {
		Expression[] args = exp.args();
		
		// Retrieve subexpressions
		// Sanity check: "and" is a binary expression
		assert(args.length == 2);
		Expression left  = args[0];
		Expression right = args[1];
		
		List<Expression> leftMutants  = strengthen(left);
		List<Expression> rightMutants = strengthen(right);
		
		// Mutation 1: Strengthen the left subexpression
		for(Expression mutant: leftMutants) {
			Expression newArgs[] = {mutant, right};
			try {
				Expression mutant1 = ExpStdOp.create("and", newArgs);
				expression.add(mutant1);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
				 
		// Mutation 2: Strengthen the right subexpression
		for(Expression mutant: rightMutants) {
			Expression newArgs[] = {left, mutant};
			try {
				Expression mutant2 = ExpStdOp.create("and", newArgs);
				expression.add(mutant2);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}	
		}
					
		// Mutation 3: Strengthen both subexpressions
		for(Expression mutantA: leftMutants) {
			for (Expression mutantB: rightMutants) {
				Expression newArgs[] = {mutantA, mutantB};
				try {
					Expression mutant3 = ExpStdOp.create("and", newArgs);
					expression.add(mutant3);
				} catch (ExpInvalidException e) {
					e.printStackTrace();
				}
			}
		}
	}
		
	private void mutateXorExp(ExpStdOp exp) {
		Expression[] args = exp.args();
		
		// Retrieve subexpressions
		// Sanity check: "xor" is a binary expression
		assert(args.length == 2);
		Expression left  = args[0];
		Expression right = args[1];
		
		// No need to mutate subexpressions - it would not be a strengthening
		// Mutation 1: replace the expression with (left & ( not right))
		try {
			Expression args1[] = {right};
			Expression aux  = ExpStdOp.create("not", args1);
			Expression args2[] = {left, aux};
			Expression mutant1 = ExpStdOp.create("and", args2); 
			expression.add(mutant1);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 2: replace the expression with ((not left) & (right))
		try {
			Expression args1[] = {left};
			Expression aux  = ExpStdOp.create("not", args1);
			Expression args2[] = {aux, right};
			Expression mutant2 = ExpStdOp.create("and", args2); 
			expression.add(mutant2);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
	}
	
	private void mutateImpliesExp(ExpStdOp exp) {
		Expression[] args = exp.args();
		
		// Retrieve subexpressions
		// Sanity check: "implies" is a binary expression
		assert(args.length == 2);
		Expression left   = args[0];
		Expression right  = args[1];
		
		// Dirty hack - Rewrite a->b as (!a)||b
		// Then, strengthen that expression as a disjunction
		
		try {
			Expression args1[] = {left};
			ExpStdOp aux1 = ExpStdOp.create("not", args1);
			Expression args2[] = {aux1, right};
			ExpStdOp aux2 = ExpStdOp.create("or", args2);
			mutateOrExp(aux2);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}		
	}
	
	private void mutateNotExp(ExpStdOp exp) {
		Expression[] args = exp.args();
		
		// Retrieve subexpressions
		// Sanity check: "xor" is a binary expression
		assert(args.length == 1);
		Expression subexp  = args[0];
		
		// TODO: Uncomment this line when weakening is implemented
		// List<Expression> mutants  = WeakenVisitor.weaken(subexp);
		List<Expression> mutants = new LinkedList<Expression>();
		
		// Mutation 1: weaken the subexpression
		for(Expression mutantSubExp: mutants) {
			Expression newArgs[] = {mutantSubExp};
			try {
				Expression mutant = ExpStdOp.create("not", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		// Mutation 2: replace by "false"
		defaultStrengthening();
	}
		
	
	private void mutateIsEmptyExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "isEmpty()" is a unary operation
		assert(args.length == 1);
		Expression col  = args[0];
		
		// TODO: Uncomment his when hull is implemented
		// List<Expression> mutants = HullVisitor.hull(col);
		List<Expression> mutants = new LinkedList<Expression>();
		
		// Mutation 1: Compute the hull of the collection
		// Compute the "isEmpty()" operation on the extended collection
		for(Expression mutantCol: mutants) {
			Expression newArgs[] = {mutantCol};
			try {
				Expression mutant = ExpStdOp.create("isEmpty", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		// Mutation 2: replace by "false"
		defaultStrengthening();
	}

	private void mutateNotEmptyExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "isEmpty()" is a unary operation
		assert(args.length == 1);
		Expression col  = args[0];
		
		// TODO: Uncomment this when the kernel is implemented
		// List<Expression> mutants = KernelVisitor.kernel(col);
		List<Expression> mutants = new LinkedList<Expression>();
		
		// Mutation 1: Compute the kernel of the collection
		// Compute the "notEmpty()" operation on the reduced collection
		for(Expression mutantCol: mutants) {
			Expression newArgs[] = {mutantCol};
			try {
				Expression mutant = ExpStdOp.create("notEmpty", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		// Mutation 2: replace by "false"
		defaultStrengthening();
	}
	
	private void mutateIncludesExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "includes()" is a binary operation
		assert(args.length == 2);
		Expression col  = args[0];
		Expression elem = args[1];
		
		// TODO: Uncomment this when the kernel is implemented
		// List<Expression> mutants = KernelVisitor.kernel(col);
		List<Expression> mutants = new LinkedList<Expression>();
		
		// Mutation 1: Compute the kernel of the collection
		// Compute the "includes()" operation on the reduced collection
		for(Expression mutantCol: mutants) {
			Expression newArgs[] = {mutantCol, elem};
			try {
				Expression mutant = ExpStdOp.create("includes", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		// Mutation 2: replace by "false"
		defaultStrengthening();
	}
	
	private void mutateExcludesExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "excludes()" is a binary operation
		assert(args.length == 2);
		Expression col  = args[0];
		Expression elem = args[1];
		
		// TODO: Uncomment this when the hull is implemented
		// List<Expression> mutants = HullVisitor.hull(col);
		List<Expression> mutants = new LinkedList<Expression>();
		
		// Mutation 1: Compute the kernel of the collection
		// Compute the "includes()" operation on the reduced collection
		for(Expression mutantCol: mutants) {
			Expression newArgs[] = {mutantCol, elem};
			try {
				Expression mutant = ExpStdOp.create("excludes", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		// Mutation 2: replace by "false"
		defaultStrengthening();
	}	

	private void mutateIncludesAllExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "includesAll()" is a binary operation
		assert(args.length == 2);
		Expression baseCol  = args[0];
		Expression otherCol = args[1];
		
		// TODO: Uncomment this when the kernel/hull is implemented
		// List<Expression> baseMutants  = KernelVisitor.kernel(baseCol);
		// List<Expression> otherMutants = HullVisitor.hull(baseCol);
		List<Expression> baseMutants = new LinkedList<Expression>();
		List<Expression> otherMutants = new LinkedList<Expression>();
		
		// Mutation 1: Compute the kernel of the base collection
		for(Expression mutantCol: baseMutants) {
			Expression newArgs[] = {mutantCol, otherCol};
			try {
				Expression mutant = ExpStdOp.create("includesAll", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		// Mutation 2: Compute the kernel of the other collection
		for(Expression mutantCol: otherMutants) {
			Expression newArgs[] = {baseCol, mutantCol};
			try {
				Expression mutant = ExpStdOp.create("includesAll", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		
		// Mutation 3: Compute the kernel of the base collection and the hull of the other collection
		for(Expression baseMutant: baseMutants) {
			for(Expression otherMutant: otherMutants) {
				Expression newArgs[] = {baseMutant, otherMutant};
				try {
					Expression mutant = ExpStdOp.create("includesAll", newArgs);
					expression.add(mutant);
				} catch (ExpInvalidException e) {
					e.printStackTrace();
				
				}
			}
		}
		
		// Mutation 4: replace by "false"
		defaultStrengthening();
	}

	private void mutateExcludesAllExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "includesAll()" is a binary operation
		assert(args.length == 2);
		Expression baseCol  = args[0];
		Expression otherCol = args[1];
		
		// TODO: Uncomment this when the kernel/hull is implemented
		// List<Expression> baseMutants  = HullVisitor.hull(baseCol);
		// List<Expression> otherMutants = HullVisitor.hull(baseCol);
		List<Expression> baseMutants = new LinkedList<Expression>();
		List<Expression> otherMutants = new LinkedList<Expression>();
		
		// Mutation 1: Compute the hull of the base collection
		for(Expression mutantCol: baseMutants) {
			Expression newArgs[] = {mutantCol, otherCol};
			try {
				Expression mutant = ExpStdOp.create("excludesAll", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		// Mutation 2: Compute the hull of the other collection
		for(Expression mutantCol: otherMutants) {
			Expression newArgs[] = {baseCol, mutantCol};
			try {
				Expression mutant = ExpStdOp.create("excludesAll", newArgs);
				expression.add(mutant);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}
		}
		
		
		// Mutation 3: Compute the hull of the base collection and the hull of the other collection
		for(Expression baseMutant: baseMutants) {
			for(Expression otherMutant: otherMutants) {
				Expression newArgs[] = {baseMutant, otherMutant};
				try {
					Expression mutant = ExpStdOp.create("excludesAll", newArgs);
					expression.add(mutant);
				} catch (ExpInvalidException e) {
					e.printStackTrace();
				
				}
			}
		}
		
		// Mutation 4: replace by "false"
		defaultStrengthening();
	}	

	private void mutateLessEqualExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "<=" is a binary operation
		assert(args.length == 2);
		//Expression exp1 = args[0];
		//Expression exp2 = args[1];
		
		// Mutation 1: replace "<=" by "<" 
		try {
			Expression mutant = ExpStdOp.create("<", args);
			expression.add(mutant);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 1: replace "<=" by "="
		try {
			Expression mutant = ExpStdOp.create("=", args);
			expression.add(mutant);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 3: replace by "false"
		defaultStrengthening();
	}
	
	private void mutateGreaterEqualExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "<=" is a binary operation
		assert(args.length == 2);
		//Expression exp1 = args[0];
		//Expression exp2 = args[1];
		
		// Mutation 1: replace ">=" by ">" 
		try {
			Expression mutant = ExpStdOp.create(">", args);
			expression.add(mutant);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 1: replace ">=" by "="
		try {
			Expression mutant = ExpStdOp.create("=", args);
			expression.add(mutant);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 3: replace by "false"
		defaultStrengthening();
	}

	private void mutateLessExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "<" is a binary operation
		assert(args.length == 2);
		Expression exp1 = args[0];
		Expression exp2 = args[1];
		
		// Mutation 1: add 1 to exp1 
		try {
			Expression newArgs1[] = {exp1, new ExpConstInteger(1)};
			Expression aux = ExpStdOp.create("+", newArgs1);
			Expression newArgs2[] = {aux, exp2};
			Expression mutant = ExpStdOp.create("<", newArgs2);
			expression.add(mutant);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 2: replace by "false"
		defaultStrengthening();
	}

	private void mutateGreaterExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "<" is a binary operation
		assert(args.length == 2);
		Expression exp1 = args[0];
		Expression exp2 = args[1];
		
		// Mutation 1: add 1 to exp2 
		try {
			Expression newArgs1[] = {exp2, new ExpConstInteger(1)};
			Expression aux = ExpStdOp.create("+", newArgs1);
			Expression newArgs2[] = {exp1, aux};
			Expression mutant = ExpStdOp.create(">", newArgs2);
			expression.add(mutant);
		} catch (ExpInvalidException e) {
			e.printStackTrace();
		}
		
		// Mutation 2: replace by "false"
//		defaultStrengthening();
	}
	
	private void mutateNotEqualsExp(ExpStdOp exp) {
		Expression[] args = exp.args();

		// Retrieve subexpressions
		// Sanity check: "<>" is a binary operation
		assert(args.length == 2);
		Expression exp1 = args[0];
		Expression exp2 = args[1];
		
		// If this is a numeric comparison, we can mutate it 
		// by replacing it with > or <
		// Otherwise we can only mutate it to false
		if (exp1.type().isKindOfNumber(Type.VoidHandling.EXCLUDE_VOID) && 
			exp2.type().isKindOfNumber(Type.VoidHandling.EXCLUDE_VOID)) {
			try {
				// Mutation 1: replace "<>" by "<"
				Expression mutant1 = ExpStdOp.create("<", args);
				expression.add(mutant1);
				// Mutation 2: replace "<>" by ">"
				Expression mutant2 = ExpStdOp.create(">", args);
				expression.add(mutant2);
			} catch (ExpInvalidException e) {
				e.printStackTrace();
			}		
		} 
		
		// We can always mutate the expression to "false"
		defaultStrengthening();
	}
	private void defaultStrengthening() {

	}
	public void wrongTypeError(String type) throws RuntimeException {
		throw new RuntimeException("Visitor reached node with incorrect operation: " + type);	
	}
}
