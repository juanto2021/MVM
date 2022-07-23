package org.tzi.mvm;

import java.util.ArrayList;
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

public class MVMStatisticsVisitor implements ExpressionVisitor{

	//	private List<Expression> expression;
	private List<classes_inv> lClasses_inv;
	//	private boolean trace = false;
	private String nomClase;

	public MVMStatisticsVisitor() {
		//		expression = new LinkedList<Expression>();
		lClasses_inv = new ArrayList<classes_inv>();
	}

	public List<classes_inv> getClasses_inv(){
		return lClasses_inv;
	}

	public void setNomClase(String nom) {
		nomClase = nom;
	}

	public void analisis_exp(Expression query, Expression range,VarDeclList decl ) {
		int posiSpc = query.toString().indexOf(" ");
		String izq = query.toString().substring(1, posiSpc);

		int posiPunto = izq.toString().indexOf(".")+1;
		String atributo = izq.toString().substring(posiPunto, izq.length());

		for(VarDecl d: decl) {
			String clase ="";
			int posi2p = d.toString().indexOf(":");
			if (posi2p>0) {
				clase = d.toString().substring(posi2p+1, d.toString().length());
				guarda_clase(clase, atributo);
			}
		}
	}

	private void guarda_clase(String nameClass, String nameAttr) {
		nameClass=nameClass.trim();
		// Busca clase en lista

		int nClss = lClasses_inv.size();
		int posiCls = -1;
		boolean hallaCls = false;
		for (int nCls = 1; nCls < nClss; nCls++) {
			classes_inv clase = new classes_inv();
			clase = lClasses_inv.get(nCls);
			if (clase.getName().equals(nameClass)){
				posiCls=nCls;
				hallaCls=true;
				continue;
			}
		}
		if (!hallaCls) {
			// Si la clase no existe, se incluye
			classes_inv clase = new classes_inv();
			clase.setName(nameClass);
			List<String> attrs = new ArrayList<String>();

			// Se incluye atributo tambien
			attrs.add(nameAttr);
			clase.setInv_attr(attrs);
			lClasses_inv.add(clase);
		} else {
			// Si la clave existe, se actualiza con atributos
			classes_inv clase = new classes_inv();
			clase = lClasses_inv.get(posiCls);
			List<String> attrs = new ArrayList<String>();
			attrs = clase.getInv_attr();
			// Busca atributo
			int nAttrs = attrs.size();
			//			int posiAttr = -1;
			boolean hallaAttr = false;		
			for (int nAttr = 0; nAttr < nAttrs; nAttr++) {
				if (attrs.get(nAttrs).equals(nameAttr)){
					hallaAttr=true;
					continue;
				}
			}
			if (!hallaAttr) {
				attrs.add(nameAttr);
				clase.setInv_attr(attrs);
				lClasses_inv.set(posiCls, clase);
			}
		}

		//		System.out.println("guardo clase " + nameClass + " atri " + nameAttr);	
	}

	@Override
	public void visitAllInstances(ExpAllInstances exp) {
		System.out.println("visitAllInstances");

	}

	@Override
	public void visitAny(ExpAny exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitAsType(ExpAsType exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitAttrOp(ExpAttrOp exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitBagLiteral(ExpBagLiteral exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitCollect(ExpCollect exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitCollectNested(ExpCollectNested exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitConstBoolean(ExpConstBoolean exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitConstEnum(ExpConstEnum exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitConstInteger(ExpConstInteger exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitConstReal(ExpConstReal exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitConstString(ExpConstString exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitEmptyCollection(ExpEmptyCollection exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitExists(ExpExists exp) {
		// TODO Auto-generated method stub
		System.out.println("visitExists , exp ["+exp+"]" );
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();	
		VarDeclList decl = exp.getVariableDeclarations();

		//		System.out.println("visitForAll - exp ( " + exp + ")");
		//		System.out.println("visitForAll - query ( " + query + ")");	
		//		System.out.println("visitForAll - range ( " + range + ")");	
		//		System.out.println("visitForAll - decl ( " + decl.toString() + ")");

		analisis_exp(query, range, decl);
	}

	@Override
	public void visitForAll(ExpForAll exp) {
		//		 TODO Auto-generated method stub
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();	
		VarDeclList decl = exp.getVariableDeclarations();

		//		System.out.println("visitForAll - exp ( " + exp + ")");
		//		System.out.println("visitForAll - query ( " + query + ")");	
		//		System.out.println("visitForAll - range ( " + range + ")");	
		//		System.out.println("visitForAll - decl ( " + decl.toString() + ")");

		analisis_exp(query, range, decl);

	}

	@Override
	public void visitIf(ExpIf exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitIsKindOf(ExpIsKindOf exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitIsTypeOf(ExpIsTypeOf exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitIsUnique(ExpIsUnique exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitIterate(ExpIterate exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitLet(ExpLet exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitNavigation(ExpNavigation exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitObjAsSet(ExpObjAsSet exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitObjOp(ExpObjOp exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitObjRef(ExpObjRef exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitOne(ExpOne exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitOrderedSetLiteral(ExpOrderedSetLiteral exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitQuery(ExpQuery exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitReject(ExpReject exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitWithValue(ExpressionWithValue exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitSelect(ExpSelect exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitSequenceLiteral(ExpSequenceLiteral exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitSetLiteral(ExpSetLiteral exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitSortedBy(ExpSortedBy exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitStdOp(ExpStdOp exp) {
		String opName = exp.opname();
		switch(opName) {
		case "or":
			//			expression(exp);
			break;	
		case "xor":
			//			mutateXorExp(exp); 
			break;
		case "and":
			//			mutateAndExp(exp);
			analysis_exp_std(exp);
			break;
		case "not":
			//			mutateNotExp(exp);
			break;	
		case "implies":
			//			mutateImpliesExp(exp);
			break;	
		case "=":
			// De momento no ponemos nada
			//			defaultStrengthening();
			analysis_exp_std(exp);
			break;	
		case "<=":
			//			mutateLessEqualExp(exp); 
			analysis_exp_std(exp);
			break;	
		case ">=":
			//			mutateGreaterEqualExp(exp);
			analysis_exp_std(exp);
			break;	
		case "<":
			//			mutateLessExp(exp);
			analysis_exp_std(exp);
			break;	
		case ">":
			//			mutateGreaterExp(exp);
			analysis_exp_std(exp);
			break;	
		case "<>":
			//			mutateNotEqualsExp(exp); 
			analysis_exp_std(exp);
			break;	
		case "isEmpty":
			//			mutateIsEmptyExp(exp);
			break;	
		case "notEmpty":
			//			mutateNotEmptyExp(exp);
			break;	
		case "includes":
			//			mutateIncludesExp(exp);
			break;	
		case "excludes":
			//			mutateExcludesExp(exp);
			break;	
		case "includesAll":
			//			mutateIncludesAllExp(exp);
			break;	
		case "excludesAll":
			//			mutateExcludesAllExp(exp);
			break;	
		default:
			//			wrongTypeError("unsupported operation type '" + opName + "'");
		}		

	}

	@Override
	public void visitTupleLiteral(ExpTupleLiteral exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitTupleSelectOp(ExpTupleSelectOp exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitUndefined(ExpUndefined exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitVariable(ExpVariable exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitClosure(ExpClosure exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitOclInState(ExpOclInState exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitVarDeclList(VarDeclList varDeclList) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitVarDecl(VarDecl varDecl) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitObjectByUseId(ExpObjectByUseId exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitConstUnlimitedNatural(ExpConstUnlimitedNatural exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitSelectByKind(ExpSelectByKind exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitExpSelectByType(ExpSelectByType exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitRange(ExpRange exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitNavigationClassifierSource(ExpNavigationClassifierSource exp) {
		// TODO Auto-generated method stub

	}

	private void analysis_exp_std(ExpStdOp exp) {
		Expression[] args = exp.args();

		assert(args.length == 2);
		Expression exp1 = args[0];
		Expression exp2 = args[1];

		analiza_punto(exp1);
		analiza_punto(exp2);

	}


	private void analiza_punto(Expression exp) {
		String strExp = exp.toString();

		int posiPunto = strExp.indexOf(".");
		System.out.println(exp.name() + "[" + strExp + "] posiPunto  ["+posiPunto+"]");

		if (posiPunto>-1) {
			String atributo = strExp.substring(posiPunto+1, strExp.length());
			//			System.out.println("Clase " + nomClase + " atributo [" + atributo + "]");

			// Recursivo
			MVMStatisticsVisitor visitor = new MVMStatisticsVisitor();		
			visitor.setNomClase(nomClase);
			exp.processWithVisitor(visitor);
			List<classes_inv> lClasses = new ArrayList<classes_inv>();
			lClasses = visitor.getClasses_inv();
			if (lClasses.size()==0) {
				guarda_clase(nomClase, atributo);
			}else {
				for(classes_inv clase: lClasses) {
					for(String attr: clase.getInv_attr()) {
						guarda_clase(clase.getName(), attr);
					}
				}
			}

		}
	}

	private void defaultStrengthening() {

	}

}
