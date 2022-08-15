package org.tzi.mvm;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.tzi.use.uml.mm.MAssociation;
import org.tzi.use.uml.mm.MAssociationEnd;
import org.tzi.use.uml.mm.MAttribute;
import org.tzi.use.uml.mm.MClass;
import org.tzi.use.uml.mm.MClassInvariant;
import org.tzi.use.uml.mm.MNavigableElement;
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

	public List<String> mLogs = new ArrayList<String>();
	public int mConLog=-1;
	public MClassInvariant mClassInv = null;
	public HashMap<MClass, List<KeyClassAttr>> mMapCAI = new HashMap<>();
	public HashMap<MClassInvariant, InfoInv> mMapInfoInv = new HashMap<>();
	public HashMap<MAttribute, InfoAttr> mMapInfoAttr = new HashMap<>();	
	public HashMap<MAssociation, InfoAssoc> mMapInfoAssoc = new HashMap<>();

	private static boolean debMVM=false;

	public MVMStatisticsVisitor() {
		mLogs.add("Entro en visitor ");
	}

	public void setClassInv(MClassInvariant pClassInv) {
		mClassInv=pClassInv;	
	}

	public MClassInvariant getClassInv(){
		return mClassInv;
	}

	public void setMapCAI(HashMap<MClass, List<KeyClassAttr>> pMapCAI) {
		mMapCAI=pMapCAI;
	}

	public HashMap<MClass, List<KeyClassAttr>> getMapCAI() {
		return mMapCAI;
	}

	public void setMapInfoInv(HashMap<MClassInvariant, InfoInv> pMapInfoInv) {
		mMapInfoInv=pMapInfoInv;
	}

	public HashMap<MClassInvariant, InfoInv> getMapInfoInv() {
		return mMapInfoInv;
	}

	public void setMapInfoAttr(HashMap<MAttribute, InfoAttr> pMapInfoAttr) {
		mMapInfoAttr=pMapInfoAttr;
	}

	public HashMap<MAttribute, InfoAttr> getMapInfoAttr() {
		return mMapInfoAttr;
	}

	public void setMapInfoAssoc(HashMap<MAssociation, InfoAssoc> pMapInfoAssoc) {
		mMapInfoAssoc=pMapInfoAssoc;
	}

	public HashMap<MAssociation, InfoAssoc> getMapInfoAssoc() {
		return mMapInfoAssoc;
	}

	public void setLogs(List<String> pLogs) {
		mLogs=pLogs;	
	}

	public List<String> getLogs(){
		return mLogs;
	}

	public void setConLog(int pmConLog) {
		mConLog=pmConLog;	
	}

	public int getConLog(){
		return mConLog;
	}

	public void storeLog(String log) {
		mConLog+=1;
		mLogs.add(mConLog +" - " + log);
	}
	/**
	 * Store list of attributes treated by every invariant
	 * @param inv
	 * @param attr
	 */
	public void storeInfoInvAttr(MClassInvariant inv, MAttribute attr) {
		List<MAttribute> lAttr = new ArrayList<MAttribute>();
		// If inv exist, include attribute on list
		if (mMapInfoInv.containsKey(inv)) {
			InfoInv oInfoInv = mMapInfoInv.get(inv);
			lAttr = oInfoInv.getlAttr();
			if (!lAttr.contains(attr)) {
				lAttr.add(attr);
			}
			oInfoInv.setlAttr(lAttr);
			mMapInfoInv.replace(inv, oInfoInv);
		}else {
			// If invariant does not exist, include invariant and attribute
			InfoInv oInfoInv = new InfoInv();
			lAttr.add(attr);
			oInfoInv.setlAttr(lAttr);
			mMapInfoInv.put(inv, oInfoInv);
		}

	}
	/**
	 * Store list of associations treated by every invariant
	 * @param inv
	 * @param assoc
	 */

	public void storeInfoInvAssoc(MClassInvariant inv, MAssociation assoc) {
		List<MAssociation> lAssoc = new ArrayList<MAssociation>();
		// If inv exist, include association on list
		if (mMapInfoInv.containsKey(inv)) {
			InfoInv oInfoInv = mMapInfoInv.get(inv);
			lAssoc = oInfoInv.getlAssoc();
			if (!lAssoc.contains(assoc)) {
				lAssoc.add(assoc);
			}
			oInfoInv.setlAssoc(lAssoc);
			mMapInfoInv.replace(inv, oInfoInv);
		}else {
			// If invariant does not exist, include invariant and association
			InfoInv oInfoInv = new InfoInv();
			lAssoc.add(assoc);
			oInfoInv.setlAssoc(lAssoc);
			mMapInfoInv.put(inv, oInfoInv);
		}

	}
	public void storeInfoAttrInv(MAttribute attr, MClassInvariant inv) {
		List<MClassInvariant> lInv = new ArrayList<MClassInvariant>();

		if (mMapInfoAttr.containsKey(attr)) {
			InfoAttr oInfoAttr = mMapInfoAttr.get(attr);
			lInv = oInfoAttr.getlInv();
			if (!lInv.contains(inv)) {
				lInv.add(inv);
			}
			mMapInfoAttr.replace(attr, oInfoAttr);
		}else
		{
			// Si no lo encuentra lo inserta en map
			lInv.add(inv);
			InfoAttr oInfoAttr = new InfoAttr(lInv);
			mMapInfoAttr.put(attr, oInfoAttr);
		}
	}
	public void storeInfoAssocInv(MAssociation assoc, MClassInvariant inv) {
		// busca attr en mapInfoAttr
		// si lo encuentra actualiza lista
		List<MClassInvariant> lInv = new ArrayList<MClassInvariant>();
		if (mMapInfoAssoc.containsKey(assoc)) {
			InfoAssoc oInfoAssoc = mMapInfoAssoc.get(assoc);
			lInv = oInfoAssoc.getlInv();
			if (!lInv.contains(inv)) {
				lInv.add(inv);
			}
			mMapInfoAssoc.replace(assoc, oInfoAssoc);
		}else
		{
			// Si no lo encuentra lo inserta en map
			lInv.add(inv);
			InfoAssoc oInfoAssoc = new InfoAssoc(lInv);
			mMapInfoAssoc.put(assoc, oInfoAssoc);
		}
	}	

	public void storeCAI(MClass pClass, MAttribute pAttr, MClassInvariant pInv) {
		// Busca clase en mMapCAI
		boolean existClass=false;
		List<KeyClassAttr> lKCAs = new ArrayList<KeyClassAttr>();
		List<MClassInvariant> lInvAttr = new ArrayList<MClassInvariant>();
		List<KeyAttrInv> lKAIs = new ArrayList<KeyAttrInv>();

		for (Map.Entry<MClass, List<KeyClassAttr>> entry : mMapCAI.entrySet()) {
			MClass mClass = entry.getKey();
			if (mClass.name().equals(pClass.name())) {
				existClass=true;
				lKCAs = mMapCAI.get(mClass);
				// Miramos si existe atributo
				boolean existAttr=false;
				int idxKCA=-1;
				for (KeyClassAttr kCA : lKCAs) {
					idxKCA+=1;
					lKAIs = kCA.getlAttr();
					int idxKAI=-1;
					for (KeyAttrInv kAI : lKAIs) {
						idxKAI+=1;
						if (kAI.attr.name().equals(pAttr.name())) {
							existAttr=true;
							lInvAttr=kAI.getlInv();
							// Miramos si existe invariante
							boolean existInv=false;
							int idxINV=-1;
							for (MClassInvariant inv : lInvAttr) {
								idxINV+=1;
								if (inv.name().equals(pInv.name())) {
									existInv=true;
									break;
								}
							}
							if (!existInv){
								lInvAttr.add(pInv); 
								kAI.setlInv(lInvAttr);
							}
							lKAIs.set(idxKAI, kAI);
							break;
						}
						// Si no existe atributo, lo insertamos
					}
					if (!existAttr){
						lInvAttr.add(pInv); 
						KeyAttrInv kAI = new KeyAttrInv(pAttr,lInvAttr);
						lKAIs.add(kAI);		
						kCA.setlAttr(lKAIs);
					}
					lKCAs.set(idxKCA, kCA);
				}
				mMapCAI.replace(mClass, lKCAs);
				break;
			}
		}

		if (!existClass){
			lInvAttr.add(pInv);
			KeyAttrInv kAI = new KeyAttrInv(pAttr,lInvAttr);

			lKAIs.add(kAI);
			// Include list of KeyAttrInv on KeyClassAttr
			KeyClassAttr kCA = new KeyClassAttr(pClass, lKAIs);

			// Add KeyClassAttr on list of KeyClassAttr
			lKCAs.add(kCA);

			// Put on Map a Class with elements finded
			mMapCAI.put(pClass, lKCAs);
		}

	}

	public MVMStatisticsVisitor preVisitor(MVMStatisticsVisitor visitor) {
		visitor.setLogs(mLogs);
		visitor.setConLog(mConLog);
		visitor.setMapCAI(mMapCAI);
		visitor.setClassInv(mClassInv);
		visitor.setMapInfoInv(mMapInfoInv);
		visitor.setMapInfoAttr(mMapInfoAttr);
		visitor.setMapInfoAssoc(mMapInfoAssoc);
		return visitor;
	}

	public MVMStatisticsVisitor postVisitor(MVMStatisticsVisitor visitor) {
		mLogs = visitor.getLogs();
		mConLog=visitor.getConLog();
		mMapCAI=visitor.getMapCAI();
		mClassInv=visitor.getClassInv();
		mMapInfoInv=visitor.getMapInfoInv();
		mMapInfoAttr=visitor.getMapInfoAttr();
		mMapInfoAssoc=visitor.getMapInfoAssoc();
		return visitor;
	}	

	@Override
	public void visitAllInstances(ExpAllInstances exp) {
		// TODO Auto-generated method stub

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
		if (debMVM) {
			System.out.println("visitAttrOp [" + exp.toString() + "] attr [" +exp.attr() +"] ");
		}
		MAttribute attr = exp.attr();
		storeLog("visitAttrOp exp ["+ exp+ "] attr["+attr+"]");
		MClass classAttr = attr.owner();
		if (debMVM) {
			System.out.println("******* Guardar clase ["+classAttr.name()+"] [" + attr.name() + "] inv [" + mClassInv.name() +"]");
		}
		storeCAI(classAttr, attr,  mClassInv);		
		storeInfoInvAttr(mClassInv,  attr);
		storeInfoAttrInv(attr,  mClassInv);
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
		doNothing();
	}

	@Override
	public void visitConstEnum(ExpConstEnum exp) {
		doNothing();
	}

	@Override
	public void visitConstInteger(ExpConstInteger exp) {
		doNothing();
	}

	@Override
	public void visitConstReal(ExpConstReal exp) {
		doNothing();
	}

	@Override
	public void visitConstString(ExpConstString exp) {
		doNothing();
	}

	@Override
	public void visitEmptyCollection(ExpEmptyCollection exp) {
		doNothing();
	}

	@Override
	public void visitExists(ExpExists exp) {
		if (debMVM) {
			System.out.println("visitExists " + exp);
		}
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();
		VarDeclList decl = exp.getVariableDeclarations();

		for (VarDecl var: decl) {
			if (debMVM) {
				System.out.println("var " + var + " " + var.name()+ " " + var.type());
			}
		}
		visitBinaryExpression (query, range);
	}

	@Override
	public void visitForAll(ExpForAll exp) {

		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();
		VarDeclList decl = exp.getVariableDeclarations();

		for (VarDecl var: decl) {
			if (debMVM) {
				System.out.println("var " + var + " " + var.name()+ " " + var.type());
			}
		}
		visitBinaryExpression (query, range);	
	}

	@Override
	public void visitIf(ExpIf exp) {
		if (debMVM) {
			System.out.println("visitIf");
		}
		Expression condition = exp.getCondition();
		Expression pElse = exp.getElseExpression();
		Expression pThen = exp.getThenExpression();

		visitTernaryExpression (condition, pElse, pThen);		
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
		if (debMVM) {
			System.out.println("visitIsUnique");
		}
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();

		visitBinaryExpression (query, range);

	}

	@Override
	public void visitIterate(ExpIterate exp) {
		if (debMVM) {
			System.out.println("visitIterate");
		}
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();

		visitBinaryExpression (query, range);		

	}

	@Override
	public void visitLet(ExpLet exp) {
		System.out.println("visitLet");
		Expression pInt = exp.getInExpression();
		Expression pVar = exp.getVarExpression();

		visitBinaryExpression (pInt, pVar);		
	}

	@Override
	public void visitNavigation(ExpNavigation exp) {

		System.out.println("Es una visitNavigation [" + exp + "]");

		MNavigableElement nav = exp.getDestination();

		MAssociation assoc = nav.association();
		List<MAssociationEnd> lMAssocEnd = assoc.associationEnds();
		MClass navClass = nav.cls();
		Expression navExp = nav.getDeriveExpression();

		Expression objExp = exp.getObjectExpression();

		visitUnaryExpression(objExp);	

		storeInfoAssocInv( assoc,  mClassInv);
		storeInfoInvAssoc(mClassInv,  assoc);
	}

	@Override
	public void visitObjAsSet(ExpObjAsSet exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitObjOp(ExpObjOp exp) {
		System.out.println("visitObjOp");
		visitMultiExpression (exp.getArguments());		
	}

	@Override
	public void visitObjRef(ExpObjRef exp) {
		System.out.println("visitObjRef");

	}

	@Override
	public void visitOne(ExpOne exp) {
		System.out.println("visitOne");
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();

		visitBinaryExpression (query, range);
	}

	@Override
	public void visitOrderedSetLiteral(ExpOrderedSetLiteral exp) {
		visitMultiExpression (exp.getElemExpr());
	}

	@Override
	public void visitQuery(ExpQuery exp) {
		System.out.println("visitQuery");
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();
		visitBinaryExpression (query, range);		

	}

	@Override
	public void visitReject(ExpReject exp) {
		System.out.println("visitReject");
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();

		visitBinaryExpression (query, range);		

	}

	@Override
	public void visitWithValue(ExpressionWithValue exp) {
		System.out.println("visitWithValue");

	}

	@Override
	public void visitSelect(ExpSelect exp) {
		System.out.println("visitSelect");
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();

		visitBinaryExpression (query, range);		
	}

	@Override
	public void visitSequenceLiteral(ExpSequenceLiteral exp) {
		System.out.println("visitSequenceLiteral");

		visitMultiExpression (exp.getElemExpr());
	}

	@Override
	public void visitSetLiteral(ExpSetLiteral exp) {

		System.out.println("visitSetLiteral");

		visitMultiExpression (exp.getElemExpr());
	}

	@Override
	public void visitSortedBy(ExpSortedBy exp) {

		System.out.println("visitSortedBy");
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();

		visitBinaryExpression (query, range);		
	}

	@Override
	public void visitStdOp(ExpStdOp exp) {
		System.out.println("Es una ExpStdOp [" + exp +"]");
		visitMultiExpression (exp.args());
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
		String varname = exp.getVarname();
		storeLog("visitVariable exp ["+ exp+ "] varname["+varname+"]");

	}

	@Override
	public void visitClosure(ExpClosure exp) {
		System.out.println("visitClosure");
		Expression query = exp.getQueryExpression();
		Expression range = exp.getRangeExpression();

		visitBinaryExpression (query, range);
	}

	@Override
	public void visitOclInState(ExpOclInState exp) {
		System.out.println("visitOclInState");
		Expression source = exp.getSourceExpr();

		visitUnaryExpression(source);
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
		System.out.println("visitObjectByUseId");
		Expression idExp = exp.getIdExpression();

		visitUnaryExpression(idExp);
	}

	@Override
	public void visitConstUnlimitedNatural(ExpConstUnlimitedNatural exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visitSelectByKind(ExpSelectByKind exp) {

		System.out.println("visitSelectByKind");
		Expression source = exp.getSourceExpression();

		visitUnaryExpression(source);
	}

	@Override
	public void visitExpSelectByType(ExpSelectByType exp) {
		System.out.println("visitExpSelectByType");
		Expression source = exp.getSourceExpression();

		visitUnaryExpression(source);

	}

	@Override
	public void visitRange(ExpRange exp) {
		System.out.println("visitRange");
		Expression pEnd = exp.getEnd();
		Expression pStart = exp.getStart();

		visitBinaryExpression (pEnd, pStart);
	}

	@Override
	public void visitNavigationClassifierSource(ExpNavigationClassifierSource exp) {
		// TODO Auto-generated method stub
		System.out.println("visitNavigationClassifierSource [" + exp + "]");
		MNavigableElement nav = exp.getDestination();
		MAssociation assoc = nav.association();
		MClass navClass = nav.cls();
		// ojo porque con navexp entramos en un bucle infinito al llamar a visitor
		Expression navExp = nav.getDeriveExpression();

		Expression objExp = exp.getObjectExpression();

		visitUnaryExpression(objExp);
	}
	public void visitUnaryExpression(Expression exp) {
		MVMStatisticsVisitor visitor = new MVMStatisticsVisitor();
		visitor = preVisitor( visitor);
		exp.processWithVisitor(visitor);
		visitor = postVisitor(visitor);
	}
	public void visitBinaryExpression (Expression exp1, Expression exp2) {
		visitUnaryExpression(exp1);
		visitUnaryExpression(exp2);		
	}	
	public void visitTernaryExpression (Expression exp1, Expression exp2, Expression exp3) {
		visitUnaryExpression(exp1);
		visitUnaryExpression(exp2);
		visitUnaryExpression(exp3);		
	}		
	public void visitMultiExpression (Expression[] exp) {
		int nArgs = exp.length;
		for (int nArg = 0; nArg < nArgs; nArg++) {
			Expression expSingle=exp[nArg];
			visitUnaryExpression(expSingle);
		}		
	}	
	public void doNothing() {
		// No hacer nada
	}
}
