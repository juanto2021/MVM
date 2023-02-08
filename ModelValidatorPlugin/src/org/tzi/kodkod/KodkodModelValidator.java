package org.tzi.kodkod;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;

import org.apache.log4j.Logger;
import org.tzi.kodkod.helper.LogMessages;
import org.tzi.kodkod.model.iface.IClass;
import org.tzi.kodkod.model.iface.IInvariant;
import org.tzi.kodkod.model.iface.IModel;
import org.tzi.mvm.CollectionCmb;
import org.tzi.mvm.Combination;
import org.tzi.mvm.ConfigMVM;
import org.tzi.mvm.InfoAssoc;
import org.tzi.mvm.InfoAttr;
import org.tzi.mvm.InfoInv;
import org.tzi.mvm.KeyAttrInv;
import org.tzi.mvm.KeyClassAttr;
import org.tzi.mvm.MVMStatisticsVisitor;
import org.tzi.mvm.ParamDialogValidator;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.kodkod.plugin.gui.ValidatorMVMDialogSimple;
import org.tzi.use.main.Session;
import org.tzi.use.uml.mm.MAssociation;
import org.tzi.use.uml.mm.MAttribute;
import org.tzi.use.uml.mm.MClass;
import org.tzi.use.uml.mm.MClassInvariant;
import org.tzi.use.uml.mm.MModel;
import org.tzi.use.uml.ocl.expr.Expression;

import kodkod.engine.Evaluator;
import kodkod.engine.Solution;
import kodkod.engine.Statistics;

/**
 * Abstract base class for all validation functionalities.
 * 
 * @author Hendrik Reitmann 
 *         modified by Juanto.
 */ 
public abstract class KodkodModelValidator {

	private static final Logger LOG = Logger.getLogger(KodkodModelValidator.class);

	protected IModel model;
	protected Session session;
	protected Solution solution;
	protected Evaluator evaluator;

	public static Collection<IInvariant> invClassTotal = new ArrayList<IInvariant>();

	public static HashMap<String, String> listCmb = new HashMap<>();
	public static HashMap<String, String> listCmbSel = new HashMap<>();
	public static HashMap<String, ResInv> mapInvRes = new HashMap<>();

	public static HashMap<MClass, List<KeyClassAttr>> mapCAI = new HashMap<>();	// Class, Attribute, invariants
	public static HashMap<MClassInvariant, InfoInv> mapInfoInv = new HashMap<>();	
	public static HashMap<MAttribute, InfoAttr> mapInfoAttr = new HashMap<>();	
	public static HashMap<MAssociation, InfoAssoc> mapInfoAssoc = new HashMap<>();
	public static HashMap<MClassInvariant, Set<MClassInvariant>> mapInfoInvSet = new HashMap<>();

	public static Set<MClassInvariant> colInvFault = new HashSet<MClassInvariant>();

	public static List<String> listSatisfiables = new ArrayList<String>();
	public static List<String> listUnSatisfiables = new ArrayList<String>();


	public static int longInvs;
	public static List<Combination> listCmbH = new ArrayList<Combination>();
	//	public static List<Combination> listCmbHB = new ArrayList<Combination>();
	public static CollectionCmb listCmbHB = new CollectionCmb();
	// JGCH Objeto coleccion
	public static CollectionCmb listSatisfiablesCH = new CollectionCmb();
	public static CollectionCmb listUnSatisfiablesCH = new CollectionCmb();

	public static List<BitSet> lBitCmbSAT= new ArrayList<BitSet>();
	public static List<BitSet> lBitCmbUNSAT= new ArrayList<BitSet>();
	
	private static IInvariant tabInv[];
	private static MClassInvariant tabInvMClass[];	

	private static Map<String,List<MAttribute>> matP;
	private static int matProb[][];
	private static MClassInvariant invXazar;
	private static String fmt = "";
	private static int numIterGreedy = ConfigMVM.getNumIter();
	private static boolean debMVM = ConfigMVM.getDebMVM();
	private static String logTime = "";
	private static Duration timeElapsedIndividual=null;

	/**
	 * Show the result of NOT repeated combinations
	 */
	public static boolean showStructuresAO  = false; // Analysis OCL
	public static boolean showSummarizeResults  = true;
	public static boolean showSatisfiables = false;
	public static boolean showUnsatisfiables = false;
	public static boolean showOthers = false;	

	public static int numCallSolver=0;
	public static int numCallSolverSAT=0;
	public static int numCallSolverUNSAT=0;

	public IModel getIModel() {
		return model;
	}
	public Session getSession() {
		return session;
	}
	/**
	 * Shows the combinations to send to the validator
	 */
	public static boolean showCmbSendToValidator  = true;

	public static Map<Integer, IInvariant> samples = new HashMap<>();

	public static List<BitSet> lBitCmb= new ArrayList<BitSet>();


	/**
	 * Validates the given model.
	 * 
	 * @param model
	 */
	public void validate(IModel model) {
		this.model = model;
		evaluator = null;

		KodkodSolver kodkodSolver = new KodkodSolver();
		if (debMVM) {
			LOG.info("MVM: Llama a solver desde validate en KodkodModelValidator");
		}

		try {
			solution = kodkodSolver.solve(model);
		} catch (Exception e) {
			LOG.error(LogMessages.validationException + " (" + e.getMessage() + ")");
			return;
		} catch (OutOfMemoryError oome) {
			LOG.error(LogMessages.validationOutOfMemory + " (" + oome.getMessage() + ")");
			return;
		}
		LOG.info(solution.outcome());
		LOG.info("MVM: Llega solution en validate en KodkodModelValidator " + solution.outcome());
		Statistics statistics = solution.stats();
		LOG.info(LogMessages.kodkodStatistics(statistics));
		switch (solution.outcome()) {
		case SATISFIABLE:
			storeEvaluator(kodkodSolver);
			satisfiable();
			break;
		case TRIVIALLY_SATISFIABLE:
			storeEvaluator(kodkodSolver);
			trivially_satisfiable();
			break;
		case TRIVIALLY_UNSATISFIABLE:
			trivially_unsatisfiable();
			break;
		case UNSATISFIABLE:
			unsatisfiable();
			break;
		default:
			throw new IllegalStateException("Kodkod returned unknown solution outcome.");
		}
		if(KodkodQueryCache.INSTANCE.isQueryEnabled()){ 
			KodkodQueryCache.INSTANCE.setEvaluator(evaluator); 
		}
	}

	/**
	 * Validates the given model.
	 * 
	 * @param model
	 */
	public void validateVariable(IModel model, MModel mModel, Session session, String tipoSearchMSS ) {
		// Save initial time to later calculate the time it takes
		Instant start = Instant.now();
		logTime="";
		this.model = model;
		this.session=session;
		evaluator = null;
		listCmb.clear();
		listCmbSel.clear();
		mapInvRes.clear();
		samples.clear();
		colInvFault.clear();

		invClassTotal.clear();
		listSatisfiables.clear();
		listUnSatisfiables.clear();

		// JGCH
		listSatisfiablesCH.clear();
		listUnSatisfiablesCH.clear();
		
		lBitCmbSAT.clear();
		lBitCmbUNSAT.clear();
		
		numCallSolver=0;
		numCallSolverSAT=0;
		numCallSolverUNSAT=0;

		KodkodSolver kodkodSolver = new KodkodSolver();

		Collection<IInvariant> invClassSatisfiables = new ArrayList<IInvariant>();
		Collection<IInvariant> invClassUnSatisfiables = new ArrayList<IInvariant>();
		Collection<IInvariant> invClassOthers = new ArrayList<IInvariant>();

		int nOrdenInv=0;
		try {
			if (debMVM) {
				LOG.info("MVM: (2) Llama a solver desde validateVariable en KodkodModelValidator. Model ("+model.name()+")");
			}
			LOG.info("MVM: Analysis of invariants individually.");
			Instant start0 = Instant.now();
			int nin=0;// provis

			for (IClass oClass: model.classes()) {
				invClassTotal.addAll(oClass.invariants());
				for (IInvariant oInv: oClass.invariants()) {
					nin+=1;
					dispMVM(nin+ " - ["+oClass.name()+"] - ["+oInv.name()+"]");
				}
			}
			longInvs = String.valueOf(invClassTotal.size()).length();

			tabInv = new IInvariant[invClassTotal.size()];
			tabInvMClass = new MClassInvariant[invClassTotal.size()];	
			// First pass to see which invariants are no longer satisfiable even if they are alone
			for (IInvariant invClass: invClassTotal) {
				tabInv[nOrdenInv] = invClass;
				for (MClassInvariant invMClass: mModel.classInvariants()) {
					if (invMClass.name().equals(invClass.name())&& invMClass.cls().name().equals(invClass.clazz().name())) {
						tabInvMClass[nOrdenInv] = invMClass;
					}
				}

				invClass.activate(); // Activate just one
				String strCombinacion = " - [A] " + invClass.name();
				// We deactivate the others
				for (IInvariant invClass2: invClassTotal) {
					if (invClass2.name()!=invClass.name()) {
						invClass2.deactivate();
						strCombinacion += " - [I] "+ invClass2.name();
					}
				}


				Solution solution = kodkodSolver.solve(model);

				String strNameInv = invClass.clazz().name()+"::"+invClass.name();
				invClass.clazz();
				strCombinacion = "Solution: ["+ solution.outcome()+"] Clazz name: ["+ invClass.clazz().name()+ "] "+ strCombinacion;

				nOrdenInv+=1;
				dispMVM("MVM: ["+nOrdenInv+"] Invariants State: " + strCombinacion);
				ResInv invRes=null;
				dispMVM("MVM: Invariants State: " + strCombinacion);
				if (solution.outcome().toString() == "SATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_SATISFIABLE") {
					invClassSatisfiables.add(invClass);
					invRes = new ResInv(strNameInv, "SATISFIABLE", nOrdenInv,invClass);
				}else if (solution.outcome().toString() == "UNSATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_UNSATISFIABLE") {
					invClassUnSatisfiables.add(invClass);
					invRes = new ResInv(strNameInv, "UNSATISFIABLE", nOrdenInv,invClass);
					// JGH
					Set<String> invariants= new HashSet<String>();
					invariants.add(fabStrInv(nOrdenInv));
					Combination cmbH = new Combination(invariants);

					// JGCH
					listUnSatisfiablesCH.add(cmbH);
					// JGB Guardar UNSAT en lista de bit lBitCmbUNSAT
					BitSet bit=new BitSet();
					bit = combStrBitSet(cmbH.strStr());
					lBitCmbUNSAT.add(bit);						

				} else {
					//QUITAR
				}

				if (!mapInvRes.containsKey(strNameInv)) {
					mapInvRes.put(strNameInv, invRes);
				}
			}
			// hacer for para ver tabla invariantes
			if (debMVM) {
				LOG.info("Tabla de invariantes");
				for (int nInv = 0; nInv < tabInv.length; nInv++) {
					dispMVM("[" + (nInv+1)+ "] ["+ tabInv[nInv].name()+"]");
				}
			}
			Instant end0 = Instant.now();
			timeElapsedIndividual = Duration.between(start0, end0);
			LOG.info("MVM: Time taken for ins individual "+ timeElapsedIndividual.toMillis() +" milliseconds");

			// Methods. Possible calculation methods 
			// New Method 
			// We look for variables of each OCL expression
			// ************************************************************************
			if (debMVM) {
				LOG.info("MVM: Tratamiento OCL");
			}
			if (tipoSearchMSS == "G") {
				analysis_OCL(model, mModel,invClassSatisfiables, invClassUnSatisfiables,invClassOthers,start);	
			}
			if (tipoSearchMSS == "L") {
				bruteForceMethod( mModel, invClassSatisfiables, invClassUnSatisfiables,invClassOthers,start);
			}

		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	/**
	 * Old Method (Leuven)
	 * This method search solutions using brute force
	 * @param mModel
	 * @param invClassSatisfiables
	 * @param invClassUnSatisfiables
	 * @param invClassOthers
	 * @param start
	 */
	private void bruteForceMethod(MModel mModel,Collection<IInvariant> invClassSatisfiables,
			Collection<IInvariant> invClassUnSatisfiables,
			Collection<IInvariant> invClassOthers,
			Instant start) {
		// Make combinations

		if (debMVM) {
			LOG.info("MVM: Inicio fabricacion de combinaciones con invariantes satisfiables.");
		}
		samples.clear();
		listSatisfiables.clear();
		listUnSatisfiables.clear();

		// JGCH
		listSatisfiablesCH.clear();
		listUnSatisfiablesCH.clear();

		lBitCmbSAT.clear();
		lBitCmbUNSAT.clear();
		
		logTime="";
		AddLogTime("prepare individual",timeElapsedIndividual);

		String strCmbBase = "";//JG

		int i = 0;
		for (IInvariant invClass: invClassSatisfiables) {
			// Search satisfiable inv in listInvRes to obtain then position
			// deberiamos poder encontrar i a partir de la alguna tabla de invs
			i = searchNumInv(invClass);
			samples.put(i, invClass);
			String cmb= String.valueOf(i);

			//JG---------------------------
			if (!strCmbBase.equals("")) {
				strCmbBase+="-";
			}
			strCmbBase+=i;
			//JG---------------------------

			// JGCH Objeto coleccion
			Set<String> invariants= new HashSet<String>();
			invariants.add(fabStrInv(cmb));
			Combination cmbH = new Combination(invariants);

			listSatisfiablesCH.add(cmbH);
			// JGB Guardar satis en lista de bit lBitCmbSAT
			BitSet bit=new BitSet();
			bit = combStrBitSet(cmb);
			lBitCmbSAT.add(bit);
			
		}

		mixInvariants(samples); 
		//JG-----------------------------------------------------------------------------------------
		// aqui1 llamar a comResto
//		System.out.println("Tam listCmbH ["+listCmbH.size()+"]");

		List<String> res = ordenaByNumInv(comResto(strCmbBase));
//		System.out.println("Tam res ["+res.size()+"]");

		// Convert Strings to BitSet
		lBitCmb= combListStrBitSet(res);
		for (BitSet cmbBit:lBitCmb) {
			//			BitSet cmbWrk = (BitSet) cmbBit.clone();
			//			cmbWrk.and(cmbBS);
			System.out.println("cmbBit " + cmbBit );

		}	
//		List<Combination> listWB = new ArrayList<Combination>();		
//		listWB.addAll(listCmbHB.values());
//		Collections.sort(listWB, new Comparator<Combination>() {
//			@Override
//			public int compare(Combination o1, Combination o2) {
//				return o2.getInvariants().size() - (o1.getInvariants().size());
//			}
//		});		
//		for (Combination cmb:listWB) {
//			System.out.println(cmb.toString());
//		}

		System.out.println("Tam listCmbHB ["+listCmbHB.size()+"]");
		//JG-----------------------------------------------------------------------------------------

		if (debMVM) {
			for (Object obj : listCmbSel.entrySet()) 
			{
				Entry<String, String> cmb= (Entry<String, String>) obj;
				String comment="";
				if (cmb.getValue().equals("N")) {
					comment = "New";
				}else {
					comment = "Detect in " +cmb.getValue();
				}
				dispMVM(String.format("%20s",cmb.getKey()) + " - " + comment);
			}
			dispMVM("");
		}

		if (debMVM) {
			LOG.info("MVM: Ordenacion de combinaciones de mayor a menor.");
		}
		Instant start6 = Instant.now();		

		// JGH
		// Ordenar cmbs de mas a menos inv
//		Collections.sort(listCmbH, new Comparator<Combination>() {
//			@Override
//			public int compare(Combination o1, Combination o2) {
//				return o2.getInvariants().size() - (o1.getInvariants().size());
//			}
//		});		

		sendToValidateCH(invClassTotal);	
		Instant end6 = Instant.now();
		Duration timeElapsed6 = Duration.between(start6, end6);
		LOG.info("MVM: Time taken for sendToValidate bruteforce: "+ timeElapsed6.toMillis() +" milliseconds");		
		AddLogTime("sendToValidate bruteforce",timeElapsed6);
		Instant end = Instant.now();
		Duration timeElapsed = Duration.between(start, end);

		// --------------------------------------------------------------------
		// Provisionalmente monto listas a partir de las nuevas estructuras
		TraspasaCH();
		LOG.info("MVM: Time taken: "+ timeElapsed.toMillis() +" milliseconds");
		AddLogTime("bruteforce TOTAL",timeElapsed);
		if (showSummarizeResults) printSummarize();		

		String tipoSearchMSS="L";
		int numberIter=1;
		//-----------------
		ParamDialogValidator param = new ParamDialogValidator(
				MainWindow.instance(), 
				this,
				invClassSatisfiables, 
				invClassUnSatisfiables, 
				invClassOthers,
				listSatisfiables,
				listUnSatisfiables,
				mapInvRes,
				mModel,
				invClassTotal,
				timeElapsed,
				numCallSolver,
				numCallSolverSAT,
				numCallSolverUNSAT,
				tipoSearchMSS,
				numberIter
				);
		//------------

		ValidatorMVMDialogSimple validatorMVMDialog= 
				new ValidatorMVMDialogSimple(param);		
		System.out.println();
		System.out.println(logTime);
	}
	private static List<BitSet> combListStrBitSet(List<String> res){
		List<BitSet> lBit= new ArrayList<BitSet>();
		for (String cmb:res) {
			BitSet bit=new BitSet();
			bit = combStrBitSet(cmb);
			lBit.add(bit);
		}
		return lBit;
	}
	private static BitSet combStrBitSet(String cmb){
		BitSet bit=new BitSet();

		String[] aInvsCmb=cmb.split("-");
		int nInvsCmb = aInvsCmb.length;
		for(int nInv = 0;nInv<nInvsCmb;nInv++) {
			String strInv = aInvsCmb[nInv];
			int vInv = Integer.parseInt(strInv)-1;
			bit.set(vInv);
		}
		return bit;
	}
	private static List<String> comResto(String strRestoIn) {
		List<String> listRes = new ArrayList<String>();
		String[] aInvsResto=strRestoIn.split("-");
		int nInvsResto = aInvsResto.length;
		String invPral = aInvsResto[0];
		if (nInvsResto>1) {

			String strRestoOut = "";

			for(int nInv = 1;nInv<nInvsResto;nInv++) {
				String inv = aInvsResto[nInv];
				if (strRestoOut!="") {
					strRestoOut+="-";
				}
				strRestoOut += inv;
			}
			System.out.println(strRestoOut);
			List<String> listRec = new ArrayList<String>();
			listRec = comResto(strRestoOut);
			// Mezclar pral con el resultado
			for (String cmb:listRec) {
				String cmbRec = invPral+"-"+cmb;
				listRes.add(cmbRec);
				listRes.add(cmb);
				// JG--------------------------
				// convertir striung en array y crear combinacion
				// Incluye combination en lista general
				String[] aInvsCmb=cmbRec.split("-");
				Combination cmbRecH= new Combination(aInvsCmb);
				if (!listCmbHB.contiene(cmbRecH)) {
					listCmbHB.add(cmbRecH);
				}
				// Incluye combination en lista general
				aInvsCmb=cmb.split("-");
				Combination cmbH= new Combination(aInvsCmb);

				//				listCmbHB.add(cmbH);
				if (!listCmbHB.contiene(cmbH)) {
					listCmbHB.add(cmbH);
				}

				// JG--------------------------				
			}
		}
		// Incluir pral
		listRes.add(invPral);
		// Incluye combination en lista general
		Set<String> invariants= new HashSet<String>();
		invariants.add(fabStrInv(invPral));
		Combination cmbInvPralH = new Combination(invariants);
		//		listCmbHB.add(cmbInvPralH);
		if (!listCmbHB.contiene(cmbInvPralH)) {
			listCmbHB.add(cmbInvPralH);
		}


		return listRes;
	}
	private static List<String> ordenaByNumInv(List<String> listCmb) {
		int nOrdenMax = 100000;
		String fmtG = "%06d";	
		List<String> listWork = new ArrayList<String>();
		List<String> listRes = new ArrayList<String>();
		for (String strCmb: listCmb) {
			String[] aInvs=strCmb.split("-");
			int nInvs = aInvs.length;
			int nOrden = nOrdenMax-nInvs;
			String iGroupF = String.format(fmtG,nOrden);	
			String newCmb = iGroupF + "/" + strCmb;
			listWork.add(newCmb);
		}
		Collections.sort(listWork);
		for (String wInv:listWork) {
			String[] aWinvs=wInv.split("/");
			String cmb = aWinvs[1];
			listRes.add(cmb);
		}

		return listRes;
	}	


	public static void TraspasaCH() {
		listSatisfiables.clear();//Provis
		listUnSatisfiables.clear();//Provis

		List<Combination> listSatCH = new ArrayList<Combination>();		
		listSatCH.addAll(listSatisfiablesCH.values());
		Collections.sort(listSatCH, new Comparator<Combination>() {
			@Override
			public int compare(Combination o1, Combination o2) {
				return o2.getInvariants().size() - (o1.getInvariants().size());
			}
		});					
		for (Combination cmb:listSatCH) {
			listSatisfiables.add(cmb.strStr());
		}

		List<Combination> listUnSatCH = new ArrayList<Combination>();		
		listUnSatCH.addAll(listUnSatisfiablesCH.getList());
		Collections.sort(listUnSatCH, new Comparator<Combination>() {
			@Override
			public int compare(Combination o1, Combination o2) {
				return o2.getInvariants().size() - (o1.getInvariants().size());
			}
		});					
		for (Combination cmb:listUnSatCH) {
			listUnSatisfiables.add(cmb.strStr());
		}				
	}

	public static String fabStrInv(String stInv) {
		String strInv ="";
		if (!stInv.equals("")) {
			String fmt = "%0"+String.valueOf(longInvs)+"d";
			strInv = String.format(fmt,Integer.parseInt(stInv));
		}
		return strInv;
	}		
	public static String fabStrInv(int nInv) {
		String strInv ="";
		String fmt = "%0"+String.valueOf(longInvs)+"d";
		strInv = String.format(fmt,nInv);
		return strInv;
	}	
	/**
	 * New calculation method trying to avoid Solver
	 * @param iModel
	 * @param mModel
	 * @param invClassSatisfiables
	 * @throws Exception 
	 */

	private void analysis_OCL(IModel iModel,MModel mModel,
			Collection<IInvariant> invClassSatisfiables,
			Collection<IInvariant> invClassUnSatisfiables,
			Collection<IInvariant> invClassOthers,			
			Instant start) throws Exception {
		logTime="";
		AddLogTime("prepare individual",timeElapsedIndividual);
		LOG.info("MVM: Analysis OCL (Greedy) - Start.");

		fmt = "%0"+String.valueOf(invClassTotal.size()).length()+"d";
		Instant end;
		Duration timeElapsed;
		String tipoSearchMSS="G";			

		// In this point We must to treat only the invariants that are satisfiables alone
		// Make col collection and strCmbTotal
		Collection<MClassInvariant> col = new ArrayList<MClassInvariant>();
		col = makeCollectionInvs(invClassSatisfiables);

		Set<String> invariants= new HashSet<String>();
		Combination cmbTotalH = new Combination(invariants);
		cmbTotalH = makeTotalCmbCH(col);

		CollectionCmb resGreedyCH = new CollectionCmb();
		List<Combination> listResGreedyCH = new ArrayList<Combination>(); 

		if (cmbTotalH.getInvariants().size()>0) {			

			Instant start2 = Instant.now();
			cmbTotalH.sortCombination();

			// Here We have a collection of MClassInvariant all them satisfiables
			buildTreeVisitor(col);

			// Preparation of Map of invariants with Set of invariants
			// Un inv esta relacionado con otro porque utiliza atributos o asociaciones comunes
			preparaMapInfoInvSet();

			Instant end2 = Instant.now();
			Duration timeElapsed2 = Duration.between(start2, end2);
			LOG.info("MVM: Time taken for Visitor: "+ timeElapsed2.toMillis() +" milliseconds");
			AddLogTime("Visitor",timeElapsed2);

			// Prepara tabla atributos comunes por cada pareja de invariantes
			preparaProbMat(mModel.classInvariants());

			// Muestra estructuras resultantes del Visitor
			if (showStructuresAO) {
				printStructuresAO();
			}

			// Calcula una combinacion base segun metodo Greedy

			String strCmbBase ="";

			// JGH
			invariants= new HashSet<String>();
			Combination cmbBaseH = new Combination(invariants);			

			// modeG = "R", se usa random para empezar por una invariante
			// modeG = "N", se usa random para empezar por una invariante			
			// modeG = "T" se usan todas las invariantes para unir resultados
			String modeG="T";// Get the best results
			modeG="T";//Pruebas
			if (debMVM) {
				LOG.info("MVM: Start Greedy");
			}

			int iIni, iFin;
			if (modeG.equals("R")) {
				iIni=0;
				iFin=1;
			}else if (modeG.equals("N")) {
				iIni=0;
				iFin=numIterGreedy; // cambiar por numero de ocurrencias variable obtenido por parametro
			}else {
				iIni=0;
				iFin=col.size();	
			}
			Instant start3 = Instant.now();
			for(int nInv=iIni;nInv<iFin;nInv++) {
				int nInvTratar=nInv;
				cmbBaseH=bucleGreedyCH(modeG, col, nInvTratar);
				dispMVM("strCmbBase ("+nInv+") ["+strCmbBase+"]");
				resGreedyCH.add(cmbBaseH);
				dispMVM(nInv + " 1 - Hay listSatisfiablesCH ["+listSatisfiablesCH.size()+"]");
			}

			// JGH
			invariants= new HashSet<String>();

			// JGH
			// Ordenar cmbs de mas a menos inv
			listResGreedyCH.addAll(resGreedyCH.getList());
			Collections.sort(listResGreedyCH, new Comparator<Combination>() {
				@Override
				public int compare(Combination o1, Combination o2) {
					return o2.getInvariants().size() - (o1.getInvariants().size());
				}
			});	
			Instant end3 = Instant.now();
			Duration timeElapsed3 = Duration.between(start3, end3);
			LOG.info("MVM: Time taken for Greedy: "+ timeElapsed3.toMillis() +" milliseconds");
			AddLogTime("Greedy",timeElapsed3);

		}// provisional a ver ...
		LOG.info("MVM: Analysis OCL (Greedy) - End.");

		end = Instant.now();
		timeElapsed = Duration.between(start, end);

		// Provisionalmente monto listas a partir de las nuevas estructuras
		TraspasaCH();		
		LOG.info("MVM: Time taken for analysis_OCL (1): "+ timeElapsed.toMillis() +" milliseconds");
		AddLogTime("analysis_OCL (1)",timeElapsed);

		tipoSearchMSS="G";	
		int numberIter=numIterGreedy;


		// Send to MVMDialogSimple
		ValidatorMVMDialogSimple validatorMVMDialog = showDialogMVM(invClassSatisfiables, 
				invClassUnSatisfiables, 
				invClassOthers,
				mModel,
				timeElapsed,
				tipoSearchMSS,
				numberIter);

		if (listSatisfiablesCH.size()>0) {
			LanzacalculoBckCH(resGreedyCH, cmbTotalH, validatorMVMDialog, start );
		}
	}
	private void AddLogTime(String txtLog, Duration timeElapsed) {
		if (!logTime.equals("")) {
			logTime+="\n";
		}
		String textoFormateado = String.format("%-25s", txtLog);
		System.out.println("[" + textoFormateado + "]");	
		String numeroFormateado = String.format("%10d", timeElapsed.toMillis());
		logTime+=textoFormateado + "  "+numeroFormateado +" milliseconds";
	}

	/**
	 * Launches the calculation of the rest of the combinations in the background
	 * @param resGreedy
	 * @param strCmbTotal
	 * @param validatorMVMDialog
	 * @param start
	 * @throws Exception
	 */

	private void LanzacalculoBckCH(CollectionCmb resGreedyCH, Combination cmbTotalCH, ValidatorMVMDialogSimple validatorMVMDialog, Instant start ) throws Exception{
		dispMVM("Inicio back");
		LOG.info("MVM: Background (Greedy) CH - Start.");
		Instant start4 = Instant.now();

		EventThreads hilo1 = new EventThreads(false) {
			@Override
			public void operacionesRun() {
				dispMVM("Lanzamos operaciones en tarea background");
				try {
					calculateInBackGroundCH(resGreedyCH, cmbTotalCH, validatorMVMDialog, start );
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		};

		hilo1.addListenerStarted(new EventThreads.IEventStarted() {
			@Override
			public void started() {
				dispMVM("Arranca tarea background");
			}
		});

		hilo1.addListenerEnded(new EventThreads.IEventEnded() {
			@Override
			public void finalizado() {
				dispMVM("Finaliza tarea background CH");
				LOG.info("MVM: Background (Greedy) CH - End.");
				Instant end4 = Instant.now();
				Duration timeElapsed4 = Duration.between(start4, end4);
				LOG.info("MVM: Time taken for LanzacalculoBckCH: "+ timeElapsed4.toMillis() +" milliseconds");	
				AddLogTime("LanzacalculoBckCH",timeElapsed4);
				try {
					Instant end = Instant.now();
					Duration timeElapsed = Duration.between(start, end);

					// Provisionalmente monto listas a partir de las nuevas estructuras
					TraspasaCH();
					LOG.info("MVM: Time taken for analysis_OCL (2): "+ timeElapsed.toMillis() +" milliseconds");
					AddLogTime("analysis_OCL (2)",timeElapsed4);
					if (showSummarizeResults) printSummarize();	

					validatorMVMDialog.updateInfo(listSatisfiables,listUnSatisfiables,
							timeElapsed, numCallSolver, numCallSolverSAT, numCallSolverUNSAT);

					System.out.println();
					System.out.println(logTime);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});

		hilo1.start();
	}
	/**
	 * Calculation of the rest of the combinations in the background
	 * @param resGreedy
	 * @param strCmbTotal
	 * @param validatorMVMDialog
	 * @param start
	 * @throws Exception
	 */

	private void calculateInBackGroundCH(CollectionCmb resGreedyCH, Combination cmbTotalCH, ValidatorMVMDialogSimple validatorMVMDialog, Instant start ) throws Exception {

		Combination cmbBaseH = new Combination();

		for(Combination cmbGreedy:resGreedyCH.getList()) {			

			cmbBaseH = new Combination();	
			cmbBaseH.setInvariants(cmbGreedy.getInvariants());

			Combination cmbResto = new Combination();
			cmbResto = makeRestCmbCH(cmbBaseH, cmbTotalCH);

			CollectionCmb colResGral = new CollectionCmb();
			CollectionCmb colResSat = new CollectionCmb();

			colResGral.add(cmbBaseH);

			Combination newCmbResto = new Combination();
			newCmbResto=cmbResto;

			int ordenBucle=0;
			while(newCmbResto.getInvariants().size()>0) {
				ordenBucle+=1;

				String aInvsRestoCH[] = new String[newCmbResto.getInvariants().size()];
				newCmbResto.getInvariants().toArray(aInvsRestoCH);

				int nInvsR = aInvsRestoCH.length;	
				newCmbResto = new Combination();
				colResSat.clear();

				for (Combination combCmbRG: colResGral.values()) {
					Combination combCmbA = new Combination();
					combCmbA.setInvariants(combCmbRG.getInvariants());
					String cmbA = combCmbA.strStr();
					for(int nInvR = 0;nInvR<nInvsR;nInvR++) {
						String invR = aInvsRestoCH[nInvR];
						invR = String.format(fmt,Integer.parseInt(invR));
						// si invR esta dentro de cmbA no se guarda
						boolean guardar=true;
						String[] aInvsA=cmbA.split("-");
						String aInvsACH[] = new String[combCmbA.getInvariants().size()];
						combCmbA.getInvariants().toArray(aInvsACH);

						int nInvsA = aInvsA.length;	
						for(int nInvA = 0;nInvA<nInvsA;nInvA++) {
							String pA = aInvsA[nInvA];
							if (pA.equals(invR)) {
								guardar=false;
								continue;
							}
						}

						// si invR esta dentro de combCmbA guardar debe ser false

						if (guardar) {
							String newCmb = cmbA + "-" + invR;
							newCmb=sortCmb(newCmb);					

							Combination cmbNew = new Combination();
							cmbNew.setInvariants(combCmbA.getInvariants());
							cmbNew.addInv(fabStrInv(invR));

							// parte nueva
							if (!colResSat.contiene(cmbNew)) {
								dispMVM("cmbNew [" + cmbNew + "]");
								String solucion="";
								solucion = calcularGreedyCH( cmbNew,  invClassTotal);
								if (solucion=="SATISFIABLE") {
									addSolutionGH(cmbNew, solucion);
									colResSat.add(cmbNew);
									newCmbResto.addInv(invR);
								}else {
									// Buscar por parejas
									String[] aInvsB=cmbA.split("-");
									int nInvsB = aInvsB.length;
									for (int nInvB = 1;nInvB<=nInvsB;nInvB++) {
										String invB=aInvsB[nInvB-1];
										Combination cmbInvB = new Combination();
										cmbInvB.addInv(fabStrInv(invB));

										String cmbMUS=invB + "-" + invR;
										cmbMUS = sortCmb(cmbMUS) ;

										Combination cmbMusH = new Combination();
										cmbMusH.setInvariants(cmbInvB.getInvariants());
										cmbMusH.addInv(fabStrInv(invR));

										//no detecta que cmbMusH esta en listSatisfiablesCH
										if (listSatisfiablesCH.contiene(cmbMusH)||listUnSatisfiablesCH.contiene(cmbMusH)) {
											continue;
										}

										solucion = calcularGreedyCH( cmbMusH,  invClassTotal);
										addSolutionGH(cmbMusH, solucion);

										dispMVM("cmbMUS [" + cmbMUS + "] solution " + solucion);
										dispMVM("cmbMusH [" + cmbMusH + "] solution " + solucion);
									}
								}
							}

						}
					}
				}
				colResGral.clear();
				colResGral.addAll(colResSat);
				dispMVM(ordenBucle + "Hay listSatisfiablesCH ["+listSatisfiablesCH.size()+"]");
			}
		}
		Instant end = Instant.now();
		Duration timeElapsed = Duration.between(start, end);

		// Provisionalmente monto listas a partir de las nuevas estructuras

		TraspasaCH();
		LOG.info("MVM: Time taken: "+ timeElapsed.toMillis() +" milliseconds");
		AddLogTime("analysis_OCL TOTAL",timeElapsed);

		if (showSummarizeResults) printSummarize();				
		validatorMVMDialog.updateInfo(listSatisfiables,listUnSatisfiables,
				timeElapsed, numCallSolver, numCallSolverSAT, numCallSolverUNSAT);	

	}
	/**
	 * Show results dialog
	 * @param invClassSatisfiables
	 * @param invClassUnSatisfiables
	 * @param invClassOthers
	 * @param mModel
	 * @param timeElapsed
	 * @param tipoSearchMSS
	 * @param numberIter
	 * @return
	 */
	private ValidatorMVMDialogSimple showDialogMVM(Collection<IInvariant> invClassSatisfiables,
			Collection<IInvariant> invClassUnSatisfiables,
			Collection<IInvariant> invClassOthers ,
			MModel mModel,
			Duration timeElapsed,
			String tipoSearchMSS,
			int numberIter) {


		//-----------------
		ParamDialogValidator param = new ParamDialogValidator(
				MainWindow.instance(), 
				this,
				invClassSatisfiables, 
				invClassUnSatisfiables, 
				invClassOthers,
				listSatisfiables,
				listUnSatisfiables,
				mapInvRes,
				mModel,
				invClassTotal,
				timeElapsed,
				numCallSolver,
				numCallSolverSAT,
				numCallSolverUNSAT,
				tipoSearchMSS,
				numberIter
				);
		//------------				

		ValidatorMVMDialogSimple validatorMVMDialog= 
				new ValidatorMVMDialogSimple(param);		
		return validatorMVMDialog;
	}

	/**
	 * Loop to be able to call Greedy randomly or for each invariant
	 * @param modeG
	 * @param col
	 * @param iTratar
	 * @return
	 */
	private Combination bucleGreedyCH(String modeG, Collection<MClassInvariant> col, int iTratar) {
		Set<String> invariants= new HashSet<String>();
		Combination cmbBaseH = new Combination(invariants);	

		List<MClassInvariant> ic = new ArrayList<MClassInvariant>();
		colInvFault.clear();
		boolean useGreedy=true;
		while (useGreedy) {
			// Calculate the combination obtained in greedyMethod

			listCmb.clear();
			listCmbH.clear();

			// ic es la lista de combinaciones que no tienen nada en comun
			ic = greedyMethod(modeG, col, iTratar);				

			dispMVM("Invariants collection (ic): " + ic.size());
			String strCmb="";//quitar
			invariants= new HashSet<String>();

			cmbBaseH = new Combination(invariants);
			for (MClassInvariant inv:ic) {
				int nCmb = searchNumInv(inv);
				if (nCmb>0) {
					if (!strCmb.equals("")) {//quitar
						strCmb=strCmb+"-";   //quitar
					}                        //quitar

					String strNinv = String.format(fmt,nCmb);//quitar
					strCmb=strCmb+strNinv;//quitar
					strCmb = sortCombination( strCmb); //quitar
					storeResult(strCmb);//quitar pero antes analizar
					cmbBaseH.addInv(fabStrInv(nCmb));
				}
			}
			cmbBaseH.sortCombination();

			String solucion="";
			if (debMVM) {
				LOG.info("MVM: Envio a calcularGreedyCH.");
			}
			solucion = calcularGreedyCH( cmbBaseH,  invClassTotal);	
			addSolutionGH(cmbBaseH, solucion);
			// si el resultado es UNSATISFIABLE y modeG = "R" hay que volver a enviarlo a greedyMethod
			// pero indicando la lista de invariantes que han fallado en las busquedas anteriores
			if (solucion.equals("SATISFIABLE")){
				useGreedy=false;
			}else {
				if (modeG.equals("R")) {
					// Si falla y el metodo es random, se vuelve a intentar
					// invXazar
					colInvFault.add(invXazar);
					// Si la coleccion de inv que fallan en greedyMethod es mayor o igual
					// a la lista de invariantes validas, detenemos busqueda para evitar 
					// bucles infinitos
					if (colInvFault.size()>= invClassTotal.size()) {
						useGreedy=false;
					}
				}else {
					// Si el metodo es total (no random) solo se intyenta una vez
					useGreedy=false;
				}
			}
		}
		return cmbBaseH;
	}	

	/**
	 * Make collection of MClassInvariants for Greedy method
	 * @param invClassSatisfiables
	 * @return
	 */
	private static Collection<MClassInvariant> makeCollectionInvs(Collection<IInvariant> invClassSatisfiables) {
		Collection<MClassInvariant> col = new ArrayList<MClassInvariant>();
		for (int nInv=0;nInv<invClassTotal.size();nInv++) {
			IInvariant inv = tabInv[nInv];
			if (invClassSatisfiables.contains(inv)) {
				MClassInvariant invClass=tabInvMClass[nInv];
				col.add(invClass);
			}
		}
		return col;
	}
	/**
	 * Build invariant relation tree using Visitor
	 * @param col
	 */
	private static void buildTreeVisitor(Collection<MClassInvariant> col) {
		if (debMVM) {
			LOG.info("MVM: working on Visitor (in)");
		}
		mapCAI.clear();
		mapInfoInv.clear();
		mapInfoAttr.clear();
		mapInfoAssoc.clear();
		int contador = 0;
		int conLog=0;
		List<String> logs = new ArrayList<String>();
		for(MClassInvariant inv: col) {

			Expression exp = inv.bodyExpression();
			MVMStatisticsVisitor visitor = new MVMStatisticsVisitor();
			// Init previous
			visitor.setLogs(logs);
			visitor.setConLog(conLog);
			visitor.setMapCAI(mapCAI);
			visitor.setMapInfoInv(mapInfoInv);
			visitor.setMapInfoAttr(mapInfoAttr);
			visitor.setMapInfoAssoc(mapInfoAssoc);
			visitor.setClassInv(inv);

			exp.processWithVisitor(visitor);

			// Collect results
			logs = visitor.getLogs();
			conLog=visitor.getConLog();
			mapCAI = visitor.getMapCAI();
			mapInfoInv=visitor.getMapInfoInv();
			mapInfoAttr=visitor.getMapInfoAttr();
			mapInfoAssoc=visitor.getMapInfoAssoc();
			contador+=1;
			dispMVM("contador [" + contador + "]");
		}
		for(String log: logs) {
			dispMVM("log [" + log + "]");
		}
		if (debMVM) {
			LOG.info("MVM: working on Visitor (out)");
		}
	}
	/**
	 * Find the order number of the invariant in the general table of invariants of the model
	 * @param inv
	 * @return
	 */
	private static int searchNumInv(MClassInvariant inv) {
		int numInvGral=-1;
		for (int nInv = 0; nInv < tabInv.length; nInv++) {
			if(inv.name().equals(tabInv[nInv].name())) {
				numInvGral=nInv+1;
				continue;
			}
		}

		if (debMVM) {
			if (numInvGral<0) {
				System.out.println("inv " + inv + " numInv<0 en searchNumInv");
			}
		}
		return numInvGral;
	}
	private static int searchNumInv(IInvariant inv) {
		int numInvGral=-1;
		for (int nInv = 0; nInv < tabInv.length; nInv++) {
			if(inv.name().equals(tabInv[nInv].name())) {
				numInvGral=nInv+1;
				continue;
			}
		}

		if (debMVM) {
			if (numInvGral<0) {
				System.out.println("inv " + inv + " numInv<0 en searchNumInv");
			}
		}
		return numInvGral;
	}	

	private static void printSummarize() {

		List<Combination> listSatCH = new ArrayList<Combination>();		
		listSatCH.addAll(listSatisfiablesCH.values());
		Collections.sort(listSatCH, new Comparator<Combination>() {
			@Override
			public int compare(Combination o1, Combination o2) {
				return o2.getInvariants().size() - (o1.getInvariants().size());
			}
		});					
		System.out.println();
		System.out.println("SAT: " + listSatisfiablesCH.size());
		for (Combination cmb:listSatCH) {
			System.out.println(cmb.strStr());
		}

		List<Combination> listUnSatCH = new ArrayList<Combination>();		
		listUnSatCH.addAll(listUnSatisfiablesCH.values());
		Collections.sort(listUnSatCH, new Comparator<Combination>() {
			@Override
			public int compare(Combination o1, Combination o2) {
				return o1.getInvariants().size() - (o2.getInvariants().size());
			}
		});					
		System.out.println();
		System.out.println("UNSAT: " + listUnSatisfiablesCH.size());
		for (Combination cmb:listUnSatCH) {
			System.out.println(cmb.strStr());
		}	

	}

	/**
	 * Prepare structure and matrix for the calculation of probabilities that one invariant interferes with another
	 * @param col
	 */
	private void preparaProbMat(Collection<MClassInvariant> col) {
		int nInvs = invClassTotal.size();		
		String strFormat="%0"+String.valueOf(nInvs).length()+"d";

		List<MAttribute> attrComun=new ArrayList<MAttribute>();
		matP = new HashMap<String,List<MAttribute>>();
		matProb = new int[nInvs][nInvs];
		for (int X=1;X<=nInvs;X++) {
			for (int Y=1;Y<=nInvs;Y++) {
				String KeyMatP = String.format(strFormat,X)+"-"+String.format(strFormat,Y);
				attrComun=new ArrayList<MAttribute>();
				matP.put(KeyMatP, attrComun);
				matProb[X-1][Y-1]=0;
			}
		}

		for (MClassInvariant invPral:col) {
			int numInvPral = searchNumInv(invPral);
			boolean revPral=true;
			// Atributos de numInvPral
			List<MAttribute> lAttrPral = new ArrayList<MAttribute>();
			if (mapInfoInv.containsKey(invPral)) {
				InfoInv oInfoInvPral = mapInfoInv.get(invPral);
				lAttrPral = oInfoInvPral.getlAttr();
			}else {
				revPral=false;
			}
			if (revPral) {
				for (MClassInvariant invRel:col) {
					int numInvRel = searchNumInv(invRel);
					// Atributos de numInvRel
					boolean revRel=true;
					List<MAttribute> lAttrRel = new ArrayList<MAttribute>();
					if (mapInfoInv.containsKey(invRel)) {
						InfoInv oInfoInvRel = mapInfoInv.get(invRel);
						lAttrRel = oInfoInvRel.getlAttr();
					}else {
						revRel=false;
					}				

					if (revRel) {
						// Miramos si ambas inv tienen relacion
						boolean bRel=false;
						if (mapInfoInvSet.containsKey(invPral)) {
							Set<MClassInvariant> lSetInvRel = new HashSet<MClassInvariant>();
							lSetInvRel=mapInfoInvSet.get(invPral);
							bRel = lSetInvRel.contains(invRel);
						}
						String KeyMatP = String.format(strFormat,numInvPral)+"-"+String.format(strFormat,numInvRel);
						String KeyMatP2 = String.format(strFormat,numInvRel)+"-"+String.format(strFormat,numInvPral);

						// Busca atributos comunes
						if (bRel) {
							attrComun = new ArrayList<MAttribute>();
							if (matP.get(KeyMatP)!=null) {
								attrComun = (List<MAttribute>) matP.get(KeyMatP);
							}
							for (MAttribute attrPral: lAttrPral) {
								// comparamos por nombre
								for (MAttribute attrRel: lAttrRel) {
									if(attrPral.name().equals(attrRel.name())) {
										if (!attrComun.contains(attrPral)) {
											attrComun.add(attrPral);
											matP.put(KeyMatP, attrComun);
											attrComun = new ArrayList<MAttribute>();
											if (matP.get(KeyMatP2)!=null) {
												attrComun = (List<MAttribute>) matP.get(KeyMatP2);
												if (!attrComun.contains(attrPral)) {
													attrComun.add(attrPral);
												}
											}
											matP.put(KeyMatP2, attrComun);
										}
									}
								}
							}
						}
					}
				}
			}
		}
		TreeMap<String, List<MAttribute>> sorted = new TreeMap<>();
		sorted.putAll(matP);
		matP=sorted;
		for (int X=1;X<=nInvs;X++) {
			for (int Y=1;Y<=nInvs;Y++) {
				String KeyMatP = String.format(strFormat,X)+"-"+String.format(strFormat,Y);
				List<MAttribute> AC=(List<MAttribute>) matP.get(KeyMatP);
				matProb[X-1][Y-1]=AC.size();
			}
		}
	}
	/**
	 * Print structures created using Visitor
	 */
	private static void printStructuresAO() {
		// Print results
		printCAI();           // Classes, Attributes & Invariants
		printMapInfoInv();    // Attributes & Assoc of Invariants 
		printMapInfoAttr();   // Invariants of Attributes
		printMapInfoAssoc();  // Invariants of Assoc
		printMapInfoInvSet(); // invariants related to invariants
		printMatProb();
	}

	/**
	 * Prints structures for the calculation of probabilities of interference between invariants
	 */
	private static void printMatProb() {
		System.out.println();
		System.out.println("Atributos comunes en invariantes relacionadas");
		System.out.println("=============================================");		
		for (Map.Entry<String,List<MAttribute>> entry : matP.entrySet()) {
			String key = entry.getKey();
			List<MAttribute> lAttrs = matP.get(key);
			if (lAttrs.size()>0) {
				System.out.println("Key ["+key+"] [" + lAttrs.size() + "] [" + lAttrs.toString() + "]");
			}
		}
		System.out.println();
		int nInvs = matProb.length;		
		String strFormat="%"+String.valueOf(nInvs).length()+"d";
		for (int X=0;X<nInvs;X++) {
			String linea="";
			if (X==0) {
				linea = String.format("%"+String.valueOf(nInvs).length()+"s","")+"  ";
				for (int Y=0;Y<nInvs;Y++) {
					String part = String.format(strFormat,Y+1);
					if (linea!="") {
						linea+="  ";
					}
					linea+=part;
				}
				System.out.println(linea);
			}
			linea = String.format(strFormat,X+1)+" -";
			for (int Y=0;Y<nInvs;Y++) {
				int nAttrComun=	matProb[X][Y];
				String part = String.format(strFormat,nAttrComun);
				if (linea!="") {
					linea+="  ";
				}
				linea+=part;
			}
			System.out.println(linea);
		}
		System.out.println("============================================");
		System.out.println("                *---*---*");
	}
	/**
	 * Print class structure, attributes, invariants
	 */
	private static void printCAI() {
		System.out.println();
		System.out.println("============================================");
		System.out.println("Class, Attributes and Invariants");
		System.out.println("============================================");
		// Classes, Attributes & Invariants
		for (Map.Entry<MClass, List<KeyClassAttr>> entry : mapCAI.entrySet()) {
			MClass mClass = entry.getKey();
			System.out.println("mClass [" + mClass.name() + "]");
			List<KeyClassAttr> lKCAs = new ArrayList<KeyClassAttr>();
			lKCAs = mapCAI.get(mClass);
			for (KeyClassAttr kCA : lKCAs) {
				System.out.println("  kCA [" + kCA.getClassAttr().name() + "]");
				List<KeyAttrInv> lKAIs = new ArrayList<KeyAttrInv>();
				lKAIs = kCA.getlAttr();
				for (KeyAttrInv kAI : lKAIs) {
					System.out.println("    kAI [" + kAI.getAttr().name() + "]");
					List<MClassInvariant> lInvAttr = new ArrayList<MClassInvariant>();
					lInvAttr=kAI.getlInv();
					if (debMVM) {
						for (MClassInvariant inv : lInvAttr) {
							System.out.println("      inv [" + inv.name() + "]");
						}
					}
				}
				System.out.println();
			}
		}
		System.out.println("============================================");
		System.out.println("                *---*---*");
	}
	/**
	 * Print mapInfoInv structure (attributes and associations of an invariant)
	 */
	private static void printMapInfoInv() {
		// Attributes & Assoc of Invariants
		System.out.println();
		System.out.println("============================================");
		System.out.println("Attributes & Assoc of Invariants");
		System.out.println("============================================");
		for (Map.Entry<MClassInvariant, InfoInv> entry : mapInfoInv.entrySet()) {
			MClassInvariant inv = entry.getKey();
			// Attributes & Assoc of Invariants
			dispMVM("inv [" + inv.name() + "]");
			List<MAttribute> lAttr = new ArrayList<MAttribute>();
			InfoInv oInfoInv = mapInfoInv.get(inv);
			// Attributes
			lAttr = oInfoInv.getlAttr();
			if (lAttr.size()>0) {
				for (MAttribute attr : lAttr) {
					dispMVM("     attr [" + attr.name() + "]");
				}				
			}
			// Assoc
			List<MAssociation> lAssoc = new ArrayList<MAssociation>();
			lAssoc = oInfoInv.getlAssoc();
			if (lAssoc.size()>0) {
				for (MAssociation assoc : lAssoc) {
					dispMVM("     assoc [" + assoc.name() + "]");
				}				
			}	
			dispMVM("");
		}
		dispMVM("============================================");
		dispMVM("                *---*---*");
	}

	/**
	 * Print mapInfoAttr structure (invariants of an attribute)
	 */
	private static void printMapInfoAttr(){
		System.out.println();
		System.out.println("============================================");
		System.out.println("Invariants of Attr");
		System.out.println("============================================");	
		for (Map.Entry<MAttribute, InfoAttr> entry : mapInfoAttr.entrySet()) {
			MAttribute attr = entry.getKey();
			System.out.println("attr [" +attr.owner().name()+ "] ["+ attr.name() + "]");
			List<MClassInvariant> lInv = new ArrayList<MClassInvariant>();
			InfoAttr InfoAttr = mapInfoAttr.get(attr);
			lInv = InfoAttr.getlInv();
			for (MClassInvariant inv : lInv) {
				dispMVM("     inv [" + inv.name() + "]");
			}
			dispMVM("");
		}		
		dispMVM("============================================");
		dispMVM("                *---*---*");
	}

	/**
	 * Print mapInfoAssoc structure (invariants of an association)
	 */
	private static void printMapInfoAssoc() {
		System.out.println();
		System.out.println("============================================");
		System.out.println("Invariants of Assoc");
		System.out.println("============================================");		
		for (Map.Entry<MAssociation, InfoAssoc> entry : mapInfoAssoc.entrySet()) {
			MAssociation assoc = entry.getKey();
			System.out.println("assoc [" + assoc.name() + "]");
			List<MClassInvariant> lInv = new ArrayList<MClassInvariant>();
			InfoAssoc oInfoAssoc = mapInfoAssoc.get(assoc);
			lInv = oInfoAssoc.getlInv();
			for (MClassInvariant inv : lInv) {
				dispMVM("     inv [" + inv.name() + "]");
			}
			dispMVM("");
		}	
		dispMVM("============================================");
		dispMVM("                *---*---*");
	}

	/**
	 * Algorithm 1 propose by Robert Clariso to find satisfiables combinations
	 * without using Solver
	 * @param col
	 * @return
	 */
	private List<MClassInvariant> greedyMethod	(String modeG, Collection<MClassInvariant> col, int nInvTratar){
		//	Preparation of Map of invariants with Set of invariants
		//  One inv is related to another because it uses common attributes or associations.		
		//	(Un inv esta relacionado con otro porque utiliza atributos o asociaciones comunes)

		List<MClassInvariant> result = new ArrayList<MClassInvariant>();

		// col -> Total collection of satisfiable invariants
		// col -> (Coleccion total de invariantes satisfiables)

		// 1. (Inicialmente nuestra combinacion de invariantes esta vacia, y) 
		//    (el conjunto de invariantes posibles es { I -> col}. Invariants possibles)
		// 1. Initially our combination of invariants is empty, and
		// the set of possible invariants is { I -> col}. possible invariants		

		Set<MClassInvariant> ic = new HashSet<MClassInvariant>(); // Invariants collection
		Set<MClassInvariant> ip = new HashSet<MClassInvariant>(); // Invariants possibles
		//		ip = col.; // Initially, ip contains all the invariants to deal with
		ip.addAll(col);
		boolean pVez=true;
		boolean searchInv=true;
		while(searchInv) {
			if (ip.size()>0) searchInv=true;
			// We can randomly search through invariants that were previously unused and failed.
			Set<MClassInvariant> ipRandom = new HashSet<MClassInvariant>();
			ipRandom.addAll(ip);
			ipRandom.removeAll(colInvFault);// Those that may have previously failed are eliminated
			if (ipRandom.size()<=0) {
				searchInv=false;
			}
			if (searchInv) {
				// We convert Set to array to get elements more easily
				int n = ipRandom.size();		
				MClassInvariant arrInv[] = new MClassInvariant[n];
				arrInv = ipRandom.toArray(arrInv);			
				// 2. (Anyadimos a nuestra combinacion un invariante X) 
				//    (elegida al azar dentro de { I -> ip}.))
				// 2. Add to our combination an invariant X
				// randomly chosen within { I -> ip}.
				if (modeG.equals("R")|| modeG.equals("N")) {
					Random random = new Random();
					int nRnd = random.nextInt(n);
					invXazar = arrInv[nRnd];
					System.out.println("["+nInvTratar+"] Random hallado ["+invXazar+"]");
				}else {
					if (pVez) {
						invXazar = arrInv[nInvTratar];
						pVez=false;
					}else {
						invXazar = arrInv[0];
					}
				}
				ic.add(invXazar);

				// 3. (Eliminamos X de { I }.)
				// 3. We remove X from { I }.				
				ip.remove(invXazar);

				// 4. (Consultamos los invariantes { Y } que tienen relacion) 
				//    ((acceden a algun elemento comun) con el invariante X.) 
				// 4. We consult the invariants { AND } that are related
				// (access some common element) with the invariant X.				
				Set<MClassInvariant> lInvY = new HashSet<MClassInvariant>();
				if (mapInfoInvSet.containsKey(invXazar)) {
					lInvY=mapInfoInvSet.get(invXazar);
					ip.removeAll(lInvY);
				}
			}
		}
		// (el ic es el conjunto "maximo" de invariantes que no tienen elementos en comun)
		// the ic is the "maximum" set of invariants that have no elements in common		
		result.addAll(ic);
		return result;

	}
	/** 
	 * Order invariants from smallest to largest by formatting with 0 from the left
	 * @param strCmb
	 * @return
	 */
	private static String sortCmb(String strCmb) {
		fmt = "%0"+String.valueOf(invClassTotal.size()).length()+"d";
		String resCmb = "";
		List<String> listRes = new ArrayList<String>();
		String[] aInvs=strCmb.split("-");
		int nInvs = aInvs.length;
		for(int nInv = 0;nInv<nInvs;nInv++) {
			String inv = aInvs[nInv];
			String invF = String.format(fmt,Integer.parseInt(inv));			
			listRes.add(invF);
		}
		Collections.sort(listRes);
		for (String inv:listRes) {
			if (resCmb!="") {
				resCmb+="-";
			}
			resCmb+=inv;
		}

		return resCmb;
	}
	/**
	 * Create String with all satisfiable combinations
	 * @param col
	 * @return
	 */

	private static Combination makeTotalCmbCH(Collection<MClassInvariant> col) {
		Set<String> invariants= new HashSet<String>();
		Combination cmbH = new Combination(invariants);			
		for (MClassInvariant invClass: col) {
			int nCmb = searchNumInv(invClass);
			invariants.add(fabStrInv(nCmb));
		}
		return cmbH;
	}	

	/**
	 * Given a base combination obtained with greedy, look for relation of invariants
	 * remaining and returns a combination with all of them
	 * @param strCmbBase
	 * @param strCmbTotal
	 * @return
	 */
	private static Combination makeRestCmbCH(Combination cmbBase, Combination cmbTotal) {
		cmbBase.sortCombination();
		cmbTotal.sortCombination();
		Combination cmbRes = new Combination();
		cmbRes = Combination.subInvs(cmbTotal, cmbBase);
		return cmbRes;
	}	

	/**
	 * Print content of mapInfoInvSet
	 */
	private static void printMapInfoInvSet() {
		System.out.println();
		System.out.println("Invariantes relacionadas entre si (mapInfoInvSet)");
		System.out.println();
		for (Map.Entry<MClassInvariant, Set<MClassInvariant>> entry : mapInfoInvSet.entrySet()) {
			MClassInvariant invKey = entry.getKey();
			dispMVM("Inv [" + invKey +"]");
			Set<MClassInvariant> lInvRrel = entry.getValue();
			for (MClassInvariant invRel: lInvRrel) {
				dispMVM("   * [" + invRel +"]");
			}
			dispMVM("");
		}
		dispMVM("============================================");
		dispMVM("                *---*---*");
	}	

	/**
	 * Preparation structure to store invariants related to each invariant
	 */
	private static void preparaMapInfoInvSet() {
		if (debMVM) {
			LOG.info("MVM: working on preparaMapInfoInvSet (in)");
		}
		// Preparo Map de invariantes con Set de invariantes
		// Un inv esta relacionado con otro porque utiliza atributos o asociaciones comunes
		mapInfoInvSet.clear();
		for (Map.Entry<MClassInvariant, InfoInv> entry : mapInfoInv.entrySet()) {
			MClassInvariant invKey = entry.getKey();
			Set<MClassInvariant> lInvRel = new HashSet<MClassInvariant>();

			dispMVM("inv [" + invKey.name() + "]");
			List<MAttribute> lAttr = new ArrayList<MAttribute>();
			InfoInv oInfoInv = mapInfoInv.get(invKey);
			// Attributes
			lAttr = oInfoInv.getlAttr();
			if (lAttr.size()>0) {
				for (MAttribute attr: lAttr) {
					List<MClassInvariant> lInv = new ArrayList<MClassInvariant>();	
					InfoAttr oInfoAttr = mapInfoAttr.get(attr);
					lInv = oInfoAttr.getlInv();
					// See each invariant and save the ones that are related to inv treated in the first loop
					// find invKey in mapInfoInvSet
					// If it is not included
					// invKey and Set of invRel
					if (!mapInfoInvSet.containsKey(invKey)) {
						lInvRel.addAll(lInv); // Remove all except invKey although it may not be necessary
						// be careful with invKey because we can be relating it
						// With Herself. That's why we removed it from its own list
						lInvRel.remove(invKey);
						mapInfoInvSet.put(invKey, lInvRel);
					}else {
						// If it is included in lInvRel the related inv

						lInvRel=mapInfoInvSet.get(invKey);
						lInvRel.addAll(lInv); 
						// We remove invKey from its own list
						lInvRel.remove(invKey);
						mapInfoInvSet.replace(invKey, lInvRel);
					}
				}
			}
		}
		if (debMVM) {
			LOG.info("MVM: working on preparaMapInfoInvSet (out)");
		}
	}



	/**
	 * Get all possible combinations
	 * @param invariantes to mix
	 */
	public  void mixInvariants(Map<Integer, IInvariant> samples) {
		Instant start5 = Instant.now();
		int nInvs = invClassTotal.size();

		// JGH
		Set<String> invariants= new HashSet<String>();
		Combination cmbH = new Combination(invariants);
		extendCH(cmbH, 1, nInvs); 

		Instant end5 = Instant.now();
		Duration timeElapsed5 = Duration.between(start5, end5);
		LOG.info("MVM: Time taken for mixInvariants: "+ timeElapsed5.toMillis() +" milliseconds");	
		AddLogTime("mixInvariants",timeElapsed5);
	}
	/**
	 * Returns Key of samples given a given order number
	 * @param samples
	 * @param orden
	 * @return
	 */
	public static int getKeyElement(Map<Integer, IInvariant> samples, int orden) {
		int j = 0;
		for(Map.Entry<Integer, IInvariant> entry : samples.entrySet()) {
			j++;
			if(j == orden) {
				return entry.getKey();
			}
		}
		return -1;
	}

	/**
	 * Recursive method that finds groups from 1 to n invariants
	 * @param base part of previous combination
	 * @param nivIni level initial
	 * @param nivMax number of invariants
	 */	
	public static void extendCH(Combination baseH, int nivIni, int nivMax) {

		if (debMVM) {
			System.out.println("Entra en extendH con baseH [" + baseH +"] nivIni [" + nivIni + "] nivMax [" + nivMax + "]");
		}
		for (int nInv = nivIni; nInv < nivMax+1; nInv++) {

			// kinv sera la clave de samples segun la posicion indicada por nInv 
			// Buscar siempre que nInv no sea unsatisfiable desde el primer momento

			// Comprobar si esta en lista de unsatisfiable (nInv+1 formateada)
			String strNinvCmp = String.format("%0"+String.valueOf(nivMax).length()+"d",nInv);
			boolean isUnsatisfiable=false;

			Set<String> invariants= new HashSet<String>();
			invariants.add(fabStrInv(strNinvCmp));
			Combination cmbCmpH = new Combination(invariants);	
			if (listUnSatisfiablesCH.contiene(cmbCmpH)) {
				isUnsatisfiable=true;
			}			
			if (!isUnsatisfiable) {
				Integer kInv = getKeyElement(samples, nInv);
				if (samples.containsKey(nInv)) {// OJO
					kInv=nInv;
					// Si nInv no esta en baseIn se guarda y se extendiende

					boolean guardar=true;

					invariants= new HashSet<String>();
					invariants.add(fabStrInv(kInv));
					Combination cmbH = new Combination(invariants);					
					guardar = !baseH.containsCmb(cmbH);

					if (guardar) {

						Set<String> invariantsX= new HashSet<String>();
						invariantsX.add(fabStrInv(kInv));
						Combination cmbK = new Combination(invariants);

						Combination cmbX = Combination.addInvs(baseH, cmbK);

						listCmbH.add(cmbX);
						if (nInv<nivMax) {
							extendCH(cmbX, nInv+1, nivMax);
						}						
					}
				}
			}
		}
	}

	/**
	 * Stores the result of a combination
	 * @param combination expression of the combination
	 */
	public static void storeResult(String combination) {
		if (listCmb.containsKey(combination)) {
			return;
		}

		// Hallar Key que le corresponde si ordenamos sus partes
		String keyOrdenada = sortCombination(combination);

		String valor="";
		// Averiguar si dicha Key ya esta usada anteriormente
		if (listCmb.containsKey(keyOrdenada)) {
			// Si esta usada, guardamos la key que la representa
			valor=combination;
			listCmb.put(combination, keyOrdenada);
			dispMVM("Encuentra " + keyOrdenada + " y guarda "+combination);
		}else {
			// Si no esta usada, almacenamos con valor 'N' (Nueva)
			valor="N";  
			listCmb.put(keyOrdenada, valor);
			listCmbSel.put(keyOrdenada, combination);
		}

		if (debMVM) {
			System.out.println(listCmb.toString());
			System.out.println(listCmbSel.toString());	
		}
	}

	/**
	 * Order the invariants within a combination
	 * @param combinacion
	 * @return
	 */
	public static String sortCombination(String combinacion) {
		String key="";
		String[] partes = combinacion.split("-");
		ArrayList<String> listaOrdenada = new ArrayList<String>(); 
		for (String parte: partes) {
			/*
			 * Simplification of parts in case they are repeated.
			 * Example: 1-1     there must be 1 since it would be the same invariant 2 times
			 *          1-2-2   should remain 1-2 since invariant 2 is repeated 2 times
			 *          1-2-1-2 should remain 1-2 since the invariants 1 and 2 are both repeated
			 */
			if (!listaOrdenada.contains(parte)){
				listaOrdenada.add(parte);
			}

		}
		Collections.sort(listaOrdenada); 
		for (String parte: listaOrdenada) {
			if (!key.equals("")) {
				key+="-";
			}
			key+=parte;
		}

		return key;
	}	

	/**
	 * Send to the validator to see if the presence of a group of invariants is satisfiable or not
	 */

	public void sendToValidateCH( Collection<IInvariant> invClassTotal) {

		int cmbSel = listCmbSel.size();
		int acumVal=0;

		if (debMVM) {
			String head="Send to Validator ("+ listCmbH +") combinations. (listSorted)";
			System.out.println(head);
			System.out.println(("-").repeat(head.length()));
		}
System.out.println("Ant [" + listCmbH.size()+ "] nueva [" + + listCmbHB.size()+"]");
		try {
			//aqui2
			List<Combination> listWB = new ArrayList<Combination>();		
			listWB.addAll(listCmbHB.values());
			Collections.sort(listWB, new Comparator<Combination>() {
				@Override
				public int compare(Combination o1, Combination o2) {
					return o2.getInvariants().size() - (o1.getInvariants().size());
				}
			});		
			for (Combination cmb:listWB) {
				System.out.println(cmb.toString());
			}			
			//			for (Combination combinacion: listCmbH) // Provis
			for (Combination combinacion: listWB)				
			{
				boolean calculateCH=true;
				// See if the combination is included in a satisfiable
				// If the join is included in some satisfiable join
				// there is no need to calculate it because it will also be satisfiable
//aqui3
				
				calculateCH = !includedInSatisfactibleCH(combinacion);

				if (calculateCH) {
					// See if there are unsatisfiable joins that are included in the join to try 
					// If the join to try contains an unsatisfiable join, it will be unsatisfiable
					calculateCH = !unsatisIncludedInCombinationCH( combinacion);
				}

				if (calculateCH) {
					// Find invariants of the combination
					String solucion="";
					try {
						solucion = calcularGreedyCH( combinacion,  invClassTotal);
					} catch (Exception e) {
						e.printStackTrace();
					}
					acumVal+=1;
					String resultado = cmbSel + " (" + acumVal+ ") " + String.format("%-20s",combinacion);
					resultado += " - ["+ solucion+"]";

					dispMVM("MVM: " + resultado);

					addSolutionGH(combinacion, solucion);
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}	
	/**
	 * Add solution of a combination to the list of Satisfiables or Unsatisfiables
	 * @param combinacion
	 * @param solution
	 */

	public void addSolutionGH(Combination combinacion, String solucion) {

		if (solucion.equals("SATISFIABLE") || solucion.equals("TRIVIALLY_SATISFIABLE")) {
			// JGCH Usando objeto para coleccion
			if (!listSatisfiablesCH.contiene(combinacion)){
				listSatisfiablesCH.add(combinacion);
				// JGB Guardar satis en lista de bit lBitCmbSAT
				BitSet bit=new BitSet();
				bit = combStrBitSet(combinacion.strStr());
				lBitCmbSAT.add(bit);
			}
		}else if (solucion.equals("UNSATISFIABLE") || solucion.equals("TRIVIALLY_UNSATISFIABLE")) {
			if (!listUnSatisfiablesCH.contiene(combinacion)){
				listUnSatisfiablesCH.add(combinacion);
				// JGB Guardar satis en lista de bit lBitCmbSAT
				BitSet bit=new BitSet();
				bit = combStrBitSet(combinacion.strStr());
				lBitCmbUNSAT.add(bit);				
			}			

		} else {
			// do nothing
		}
	}
	/**
	 * Calculate a certain combination
	 * @param combinacion
	 * @param invClassTotal
	 * @return
	 */
	public Solution calcular(String combinacion, Collection<IInvariant> invClassTotal) {
		KodkodSolver kodkodSolver = new KodkodSolver();
		if (debMVM) {
			dispMVM("MVM: Entra en calcular (" + combinacion + ")");
		}
		Solution solution=null;
		// Find invariants of the combination
		List<IInvariant> listInv = new ArrayList<IInvariant>();
		listInv=splitInvCombination( combinacion);

		// Activate only those of the combination
		String listaActivas="";
		for (IInvariant invClass: invClassTotal) {
			if (listInv.contains(invClass)) {
				invClass.activate();
				if (listaActivas != "") {
					listaActivas += "\n";
				}
				listaActivas+="    " + invClass.name();
			}else {
				invClass.deactivate();
			}
		}

		try {
			numCallSolver+=1;
			solution = kodkodSolver.solve(model);
			if (solution.outcome().toString() == "SATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_SATISFIABLE") {
				numCallSolverSAT+=1;
			}else if (solution.outcome().toString() == "UNSATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_UNSATISFIABLE") {
				numCallSolverUNSAT+=1;
			} else {

			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		return solution;
	}
	/**
	 * Calculate a certain combination (special for Greedy)
	 * @param combinacion
	 * @param invClassTotal
	 * @return
	 */	
	public String calcularGreedyCH(Combination combinacion, Collection<IInvariant> invClassTotal) {
		KodkodSolver kodkodSolver = new KodkodSolver();
		String solucion="";
		if (debMVM) {
			dispMVM("MVM: Entra en calcular (" + combinacion + ")");
		}

		// First of all see if you can deduce the result

		boolean calculateCH=true;		
		// See if the combination is included in a satisfiable
		// If the join is included in some satisfiable join
		// there is no need to calculate it because it will also be satisfiable	

		calculateCH = !includedInSatisfactibleCH(combinacion);		
		if (!calculateCH) {
			solucion="SATISFIABLE";
			return solucion;
		}
		if (calculateCH) {
			// See if there are unsatisfiable joins that are included in the join to try 
			// If the join to try contains an unsatisfiable join, it will be unsatisfiable

			calculateCH = !unsatisIncludedInCombinationCH( combinacion);
			if (!calculateCH) {
				solucion="UNSATISFIABLE";
				return solucion;
			}
		}
		// Find invariants of the combination
		List<IInvariant> listInv = new ArrayList<IInvariant>();
		listInv=splitInvCombinationH( combinacion);

		// Activate only those of the combination
		String listaActivas="";
		for (IInvariant invClass: invClassTotal) {
			if (listInv.contains(invClass)) {
				invClass.activate();
				if (listaActivas != "") {
					listaActivas += "\n";
				}
				listaActivas+="    " + invClass.name();
			}else {
				invClass.deactivate();
			}
		}

		try {
			numCallSolver+=1;
			solution = kodkodSolver.solve(model);
			if (solution.outcome().toString() == "SATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_SATISFIABLE") {
				numCallSolverSAT+=1;
				solucion="SATISFIABLE";
			}else if (solution.outcome().toString() == "UNSATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_UNSATISFIABLE") {
				numCallSolverUNSAT+=1;
				solucion="UNSATISFIABLE";
			} else {
				// do nothing
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		return solucion;
	}

	/**
	 * Find invariants of the combination
	 * @param combinacion
	 * @return
	 */
	private List<IInvariant> splitInvCombination(String combinacion) {
		List<IInvariant> listInvW = new ArrayList<IInvariant>();
		// Buscar invariantes de la combinacion
		listInvW.clear();
		String[] invs = combinacion.split("-");	
		for (String invStrID: invs) {
			int invID=Integer.parseInt(invStrID);  
			IInvariant inv = (IInvariant) tabInv[invID-1];
			listInvW.add(inv);				
		}
		return listInvW;
	}

	private List<IInvariant> splitInvCombinationH(Combination combinacion) {

		List<IInvariant> listInvW = new ArrayList<IInvariant>();
		// Buscar invariantes de la combinacion
		listInvW.clear();

		Set<String> listInvS = new HashSet<String>();
		listInvS=combinacion.getInvariants();


		String[] invs = new String[listInvS.size()];

		try {
			int index = 0;
			for (String str : listInvS) {
				invs[index] = str;
				index++;
			}

			for (String invStrID: invs) {
				int invID=Integer.parseInt(invStrID);  
				IInvariant inv = (IInvariant) tabInv[invID-1];				
				listInvW.add(inv);				
			}		
		}catch(Exception e) {
			System.out.println(e.getMessage());
		}


		return listInvW;
	}
	/**
	 * Chek if combinations exist in listSatisfiables list
	 * @param combinacion
	 * @return
	 */

	private boolean includedInSatisfactibleCH(Combination combinacion) {
		boolean bRes=false;
		bRes=listSatisfiablesCH.sameContains(combinacion);	
		if (bRes) {
			listSatisfiablesCH.add(combinacion);
			// JGB Guardar satis en lista de bit lBitCmbSAT
			BitSet bit=new BitSet();
			bit = combStrBitSet(combinacion.strStr());
			lBitCmbSAT.add(bit);
		}
		return bRes;
	}	

	/**
	 * If there is some unsatisfiable combination contained in the combination to be treated, we will say that the
	 * combination is also unsatisfiable
	 * @param combinacion
	 * @return
	 */

	private boolean unsatisIncludedInCombinationCH(Combination combinacion) {
		boolean bRes=false;
		bRes=listUnSatisfiablesCH.sameContainedIn(combinacion);	
		if (bRes) {
			listUnSatisfiablesCH.add(combinacion);
			// JGB Guardar UNSAT en lista de bit lBitCmbUNSAT
			BitSet bit=new BitSet();
			bit = combStrBitSet(combinacion.strStr());
			lBitCmbUNSAT.add(bit);				
		}			
		return bRes;		
	}	
	private static void dispMVM(String text) {
		if (debMVM) {
			System.out.println(text);
		}
	}

	/**
	 * Stores instance of kodkodSolver
	 * @param kodkodSolver
	 */

	private void storeEvaluator(KodkodSolver kodkodSolver) {
		evaluator = kodkodSolver.evaluator();
	}

	protected abstract void satisfiable();

	protected abstract void trivially_satisfiable();

	protected abstract void trivially_unsatisfiable();

	protected abstract void unsatisfiable();

}

/**
 * Class destined to store the result and comment of each combination
 * @author Juanto
 *
 */

class ResComb {
	String combinacion;
	String resultado;
	String comentario;
	public ResComb(String strCombinacion, String strResultado, String strComentario) {

		this.combinacion = strCombinacion;
		this.resultado = strResultado;
		this.comentario = strComentario;
	}
}
/**
 * Allows you to create a thread to calculate the rest of the combinations to complement the Greedy method
 * @author Juanto
 *
 */
abstract class EventThreads extends Thread {

	private List<IEventStarted> listenersStarted = new ArrayList<>();
	private List<IEventEnded> listenersEnded = new ArrayList<>();

	public EventThreads() {
		this(false);
	}

	public EventThreads(final boolean isDaemon) {
		this.setDaemon(isDaemon);
	}

	public void run () {
		for (IEventStarted o : listenersStarted) {
			o.started();
		}

		operacionesRun();

		for (IEventEnded o : listenersEnded) {
			o.finalizado();
		}
	}

	public abstract void operacionesRun();

	public void addListenerStarted(IEventStarted IEventStarted) {
		listenersStarted.add(IEventStarted);
	}

	public void removeListenerStarted(IEventStarted escuchador) {
		listenersStarted.remove(escuchador);
	}

	public void addListenerEnded(IEventEnded escuchador) {
		listenersEnded.add(escuchador);
	}

	public void removeListenerEnded(IEventEnded escuchador) {
		listenersEnded.remove(escuchador);
	}

	public interface IEventStarted {
		void started();
	}

	public interface IEventEnded {
		void finalizado();
	}
}


