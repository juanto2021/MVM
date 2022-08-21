package org.tzi.kodkod;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
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
import org.tzi.mvm.InfoAssoc;
import org.tzi.mvm.InfoAttr;
import org.tzi.mvm.InfoInv;
import org.tzi.mvm.KeyAttrInv;
import org.tzi.mvm.KeyClassAttr;
import org.tzi.mvm.MVMStatisticsVisitor;
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

	Collection<IInvariant> invClassTotal = new ArrayList<IInvariant>();

	public static HashMap<String, String> listCmb = new HashMap<>();
	public static HashMap<String, String> listCmbSel = new HashMap<>();
	public static HashMap<String, String> mapGRP_SAT_MAX = new HashMap<>();
	public static HashMap<String, ResInv> mapInvRes = new HashMap<>();

	public static HashMap<MClass, List<KeyClassAttr>> mapCAI = new HashMap<>();	
	public static HashMap<MClassInvariant, InfoInv> mapInfoInv = new HashMap<>();	
	public static HashMap<MAttribute, InfoAttr> mapInfoAttr = new HashMap<>();	
	public static HashMap<MAssociation, InfoAssoc> mapInfoAssoc = new HashMap<>();
	public static HashMap<MClassInvariant, Set<MClassInvariant>> mapInfoInvSet = new HashMap<>();

	public static Set<MClassInvariant> colInvFault = new HashSet<MClassInvariant>();

	public static List<ResComb> listCmbRes = new ArrayList<ResComb>();
	public static List<ResInv> listInvRes = new ArrayList<ResInv>();

	public static List<String> listSatisfiables= new ArrayList<String>();
	public static List<String> listUnSatisfiables= new ArrayList<String>();
	public static List<String> listUnSatisfiablesTotal= new ArrayList<String>();
	public static List<String> listOthers= new ArrayList<String>();

	private static boolean debMVM=false;

	private static IInvariant tabInv[];
	private static MClassInvariant tabInvMClass[];	

	private static Map<String,List<MAttribute>> matP;
	private static int matProb[][];
	private static MClassInvariant invXazar;

	/**
	 * Show the result of NOT repeated combinations
	 */
	public static boolean showStructuresAO  = false;
	public static boolean showSummarizeResults  = false;
	public static boolean bShowResult  = false;	
	public static boolean bShowResultGral  = false;		

	public static boolean showSatisfiables = true;
	public static boolean showUnsatisfiables = true;
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

	public static Map<Integer, IInvariant> samples;
	/**
	 * Validates the given model.
	 * 
	 * @param model
	 */
	public void validate(IModel model) {
		this.model = model;
		evaluator = null;

		KodkodSolver kodkodSolver = new KodkodSolver();
		LOG.info("MVM: Llama a solver desde validate en KodkodModelValidator");
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
		this.model = model;
		this.session=session;
		evaluator = null;
		listCmb.clear();
		listCmbSel.clear();
		listCmbRes.clear();
		mapInvRes.clear();
		samples = new HashMap<>();
		colInvFault = new HashSet<MClassInvariant>();

		invClassTotal.clear();
		listSatisfiables.clear();
		listUnSatisfiables.clear();
		listUnSatisfiablesTotal.clear();
		listOthers.clear();

		numCallSolver=0;
		numCallSolverSAT=0;
		numCallSolverUNSAT=0;

		KodkodSolver kodkodSolver = new KodkodSolver();

		Collection<IInvariant> invClassSatisfiables = new ArrayList<IInvariant>();
		Collection<IInvariant> invClassUnSatisfiables = new ArrayList<IInvariant>();
		Collection<IInvariant> invClassOthers = new ArrayList<IInvariant>();

		int nOrdenInv=0;
		try {
			LOG.info("MVM: (2) Llama a solver desde validateVariable en KodkodModelValidator. Model ("+model.name()+")");
			LOG.info("MVM: (2) Analisis de invariantes de forma individual.");

			for (IClass oClass: model.classes()) {
				invClassTotal.addAll(oClass.invariants());
			}
			tabInv = new IInvariant[invClassTotal.size()];
			tabInvMClass = new MClassInvariant[mModel.classInvariants().size()];			
			// First pass to see which invariants are no longer satisfiable even if they are alone
			for (IInvariant invClass: invClassTotal) {
				tabInv[nOrdenInv] = invClass;
				for (MClassInvariant invMClass: mModel.classInvariants()) {
					if (invMClass.name().equals(invClass.name())&& invMClass.cls().name().equals(invClass.clazz().name())) {
						tabInvMClass[nOrdenInv] = invMClass;
					}
				}

				invClass.activate();
				String strCombinacion = " - [A] " + invClass.name();
				// We disable the others
				for (IInvariant invClass2: invClassTotal) {
					if (invClass2.name()!=invClass.name()) {
						invClass2.deactivate();
						strCombinacion += " - [I] "+ invClass2.name();
					}
				}

				kodkodSolver = new KodkodSolver();
				Solution solution = kodkodSolver.solve(model);

				String strNameInv = invClass.clazz().name()+"::"+invClass.name();
				invClass.clazz();
				strCombinacion = "Solution: ["+ solution.outcome()+"] Clazz name: ["+ invClass.clazz().name()+ "] "+ strCombinacion;

				nOrdenInv+=1;

				ResInv invRes=null;
				if (debMVM) {
					System.out.println("MVM: Invariants State: " + strCombinacion);
				}
				if (solution.outcome().toString() == "SATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_SATISFIABLE") {
					invClassSatisfiables.add(invClass);
					invRes = new ResInv(strNameInv, "SATISFIABLE", nOrdenInv,invClass);
				}else if (solution.outcome().toString() == "UNSATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_UNSATISFIABLE") {
					invClassUnSatisfiables.add(invClass);
					invRes = new ResInv(strNameInv, "UNSATISFIABLE", nOrdenInv,invClass);

					int totalInv = invClassTotal.size();
					String strNOrdenInv = String.format("%0"+String.valueOf(totalInv).length()+"d",nOrdenInv);
					listUnSatisfiables.add(String.valueOf(strNOrdenInv));
				} else {
					invClassOthers.add(invClass);
					invRes = new ResInv(strNameInv, "OTHERS", nOrdenInv,invClass);
				}

				if (!listInvRes.contains(invRes)) {
					listInvRes.add(invRes);
				}
				if (!mapInvRes.containsKey(strNameInv)) {
					mapInvRes.put(strNameInv, invRes);
				}
			}
			// hacer for para ver tabla invariantes
			if (true) {
				LOG.info("Tabla de invariantes");
				for (int nInv = 0; nInv < tabInv.length; nInv++) {
					System.out.println("[" + (nInv+1)+ "] ["+ tabInv[nInv].name()+"]");
				}
			}
			// Individual Results
			if (bShowResult) {
				showResult(invClassSatisfiables,  invClassUnSatisfiables, invClassOthers);
			}

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

			//				
			// ************************************************************************
			// Old method (Leuven)
			//							bruteForceMethod( mModel, invClassSatisfiables, invClassUnSatisfiables,invClassOthers,start);
			// ************************************************************************

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
		LOG.info("MVM: Inicio fabricacion de combinaciones con invariantes satisfiables.");
		samples.clear();
		listSatisfiables.clear();
		int i = 0;
		for (IInvariant invClass: invClassSatisfiables) {
			// Search satisfiable inv in listInvRes to obtain then position
			String strNameInv = invClass.clazz().name()+"::"+invClass.name();
			if (mapInvRes.containsKey(strNameInv)) {
				ResInv invRes = (ResInv) mapInvRes.get(strNameInv);
				i=invRes.intOrden;
			}
			samples.put(i, invClass);
			String cmb= String.valueOf(i);
			listSatisfiables.add(cmb);
			storeResultCmb(cmb, "SATISFIABLE", "Direct calculation");
		}

		mixInvariants(samples); 
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

				System.out.println(String.format("%20s",cmb.getKey()) + " - " + comment);			
			}
			System.out.println();
		}
		LOG.info("MVM: Ordenacion de combinaciones de mayor a menor.");

		// Sorting list before send it to validate
		List<String> listSorted = new ArrayList<>(listCmbSel.keySet());
		List<String> listSortedByCmb = listSorted;
		// Sorting combinations by number of combinations from greatest to lowest
		listSortedByCmb = sortByCmbNumber(listSorted, invClassTotal.size());
		LOG.info("MVM: Envio a sendToValidate.");
		sendToValidate(listSortedByCmb , invClassTotal); 

		// Compact results
		// Is 1-2-3 is SAT and 1-2-4 also,  we have de group (1-2) that can be SAT with 3 or with 4
		busca_grupos_SAT_MAX();

		if (bShowResultGral) showResultGral();
		Instant end = Instant.now();
		Duration timeElapsed = Duration.between(start, end);
		LOG.info("MVM: Time taken: "+ timeElapsed.toMillis() +" milliseconds");
		ValidatorMVMDialogSimple validatorMVMDialog= 
				new ValidatorMVMDialogSimple(MainWindow.instance(), 
						this,
						invClassSatisfiables, 
						invClassUnSatisfiables, 
						invClassOthers,
						mapGRP_SAT_MAX,
						listSatisfiables,
						listUnSatisfiables,
						listOthers,
						mapInvRes,
						mModel,
						invClassTotal,
						timeElapsed,
						numCallSolver,
						numCallSolverSAT,
						numCallSolverUNSAT);
	}
	/**
	 * New calculation method trying to avoid Solver
	 * @param iModel
	 * @param mModel
	 * @param invClassSatisfiables
	 */
	private void analysis_OCL(IModel iModel,MModel mModel,
			Collection<IInvariant> invClassSatisfiables,
			Collection<IInvariant> invClassUnSatisfiables,
			Collection<IInvariant> invClassOthers,			
			Instant start) {
		samples.clear();
		// In this point We must to treat only the invariants that are satisfiables alone
		Collection<MClassInvariant> col = new ArrayList<MClassInvariant>();
		for (MClassInvariant invClass: mModel.classInvariants()) {

			for (IInvariant inv: invClassSatisfiables) {
				// Check is invariant is satisfiable
				if (invClass.name().equals(inv.name())){
					col.add(invClass);
					continue;
				}
			}
		}

		// Here We have a collection of MClassInvariant all them satisfiables

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
			if (debMVM) {
				System.out.println("contador [" + contador + "]");
			}
		}
		if (debMVM) {
			for(String log: logs) {
				System.out.println("log [" + log + "]");
			}
		}
		// Preparation of Map of invariants with Set of invariants
		// Un inv esta relacionado con otro porque utiliza atributos o asociaciones comunes
		preparaMapInfoInvSet();

		printMapInfoAttr();// quitar luego
		// Prepara tabla atributos comunes por cada pareja de invariantes
		preparaProbMat(mModel.classInvariants());
//		printMatProb();

		if (showStructuresAO) {
			// Print results
			printCAI();           // Classes, Attributes & Invariants
			printMapInfoInv();    // Attributes & Assoc of Invariants 
			printMapInfoAttr();   // Invariants of Attributes
			printMapInfoAssoc();  // Invariants of Assoc
			printMapInfoInvSet(); // invariants related to invariants
		}
//		printMatProb();


		List<MClassInvariant> ic = new ArrayList<MClassInvariant>();
		colInvFault.clear();
		boolean useGreedy=true;
		while (useGreedy) {
			// Calculate the combination obtained in greedyMethod
			samples.clear();
			listCmb.clear();
			listCmbRes.clear();

			List<String> listSorted = new ArrayList<String>();
			// ic es la lista de combinaciones que no tienen nada en comun
			ic = greedyMethod(col);				
			System.out.println("Invariants collection (ic): " + ic.size());
			String strCmb="";

			for (MClassInvariant inv:ic) {
				int nCmb=1; // Contador general
				for (IInvariant iin:invClassTotal) {
					if (iin.name().equals(inv.name())) {
						nCmb = searchNumInv(inv);
						if (nCmb>0) {
							// AQUI2

							samples.put(nCmb, iin);		
							//							samples.put(strNinv, iin);	

							if (!strCmb.equals("")) {
								strCmb=strCmb+"-";
							}
							String strNinv = String.format("%0"+String.valueOf(invClassTotal.size()).length()+"d",nCmb);
							//							strCmb=strCmb+nCmb; //buena?
							strCmb=strCmb+strNinv;
							strCmb = sortCombination( strCmb); 
							storeResult(strCmb);// nose
						}
					}
				}
			}

			listSorted.add(strCmb);
			LOG.info("MVM: Envio a sendToValidate.");
			// Send to Validate (sendToValidate)
			sendToValidate(listSorted , invClassTotal); 
			// si el resultado es UNSATISFIABLE hay que volver a enviarlo a greedyMethod
			// pero indicando la lista de invariantes que han fallado en las busquedas anteriores
			// Sabemos que es satisfiable si en la lista listSatisfiables hay resultados.
			if (listSatisfiables.size()>0) {
				useGreedy=false;
			}else {
				// invXazar
				colInvFault.add(invXazar);
				// Si la colección de inv que fallan en greedyMethod es mayor o igual
				// a la lista de invariantes validas, detenemos busqueda para evitar 
				// bucles infinitos
				if (colInvFault.size()>= invClassTotal.size()) {
					useGreedy=false;
				}
			}
		}

		// TODO 
		// En este punto, samples tiene una combinaicon satisfiable con el maximo de invariantes que se ha podido conseguir
		// Deberiamos guardar esta combinacion y volver a poblar samples con las combinaciones del resto de invariantes no tratadas
		// 1 averiguar invariantes pendientes de tratar
		// 2 Buscar samples de dicho resto de invariantes

		List<String> lResGreedy = listSatisfiables;

		String cmbGreedy = listSatisfiables.get(0);
		String[] strCmbGreedy=cmbGreedy.split("-");
		int nInvsGreedy = strCmbGreedy.length;
		//		String strCmb=strCmbGreedy[0];
		// De samples eliminamos las invariantes de ic 
		samples.clear();
		listSatisfiables.clear();
		//		listUnSatisfiables.clear();

		int i = 0;
		for (IInvariant invClass: invClassSatisfiables) {
			// busca orden 
			int nInvClass = searchNumInvII(invClass);
			// Si el orden no es una de las greedy se guarda
			boolean guardarSample=true;

			for (int nInv = 0; nInv < nInvsGreedy; nInv++) {
				int nInvGreedy = Integer.parseInt(strCmbGreedy[nInv]);
				if (nInvClass==nInvGreedy) {
					guardarSample = false;
				}
			}
			if (guardarSample) {
				samples.put(nInvClass, invClass);
				String strNinv = String.format("%0"+String.valueOf(invClassTotal.size()).length()+"d",nInvClass);
				storeResult(String.valueOf(strNinv));//???
				// aquistore

				//				String cmb= String.valueOf(nInvClass);
				//				listSatisfiables.add(cmb);// creo que no
				//				storeResultCmb(cmb, "SATISFIABLE", "Direct calculation");			
			}
		}

		// en samples pondremos el resto de invariantes no tratadas
		mixInvariants(samples); 

		List<String> listSorted = new ArrayList<>(listCmbSel.keySet());
		List<String> listSortedAmpliada = new ArrayList<>();

		// Finalmente incluiremos a cada resultado la combinacion base MSS obtenida en el paso greedy

		//aqui1
		for (String strCmb: listSorted) {

			String strNewCmb = strCmb + "-" + cmbGreedy;
			strNewCmb = sortCombination(strNewCmb); 
			listSortedAmpliada.add(strNewCmb);
			storeResult( strNewCmb);//??
		}

		List<String> listSortedByCmb = new ArrayList<>();

		//		List<String> listSortedByCmb = listSorted;
		// Sorting combinations by number of combinations from greatest to lowest
		listSortedByCmb = sortByCmbNumber(listSortedAmpliada, invClassTotal.size());		
		LOG.info("MVM: Envio a sendToValidate despues greedy.");
		// Send to Validate (sendToValidate)
		sendToValidate(listSortedAmpliada , invClassTotal); 

		busca_grupos_SAT_MAX();

		if (bShowResultGral) showResultGral();
		Instant end = Instant.now();
		Duration timeElapsed = Duration.between(start, end);
		LOG.info("MVM: Time taken: "+ timeElapsed.toMillis() +" milliseconds");

		busca_grupos_SAT_MAX();

		if (bShowResultGral) showResultGral();
		LOG.info("MVM: Time taken: "+ timeElapsed.toMillis() +" milliseconds");
		ValidatorMVMDialogSimple validatorMVMDialog= 
				new ValidatorMVMDialogSimple(MainWindow.instance(), 
						this,
						invClassSatisfiables, 
						invClassUnSatisfiables, 
						invClassOthers,
						mapGRP_SAT_MAX,
						listSatisfiables,
						listUnSatisfiables,
						listOthers,
						mapInvRes,
						mModel,
						invClassTotal,
						timeElapsed,
						numCallSolver,
						numCallSolverSAT,
						numCallSolverUNSAT);
	}
	/**
	 * Find the order number of the invariant in the general table of invariants of the model
	 * @param inv
	 * @return
	 */
	private int searchNumInv(MClassInvariant inv) {
		int numInvGral=-1;
		for (int nInv = 0; nInv < tabInv.length; nInv++) {
			if(inv.name().equals(tabInv[nInv].name())) {
				numInvGral=nInv+1;
				continue;
			}
		}
		if (numInvGral<0) {
			System.out.println("inv " + inv + " numInv<0 en searchNumInv");
		}
		return numInvGral;
	}
	/**
	 * Find the order number of the invariant in the general table of invariants of the model
	 * @param inv
	 * @return
	 */
	private int searchNumInvII(IInvariant inv) {
		int numInvGral=-1;
		for (int nInv = 0; nInv < tabInv.length; nInv++) {
			IInvariant invCmp = tabInv[nInv];
			if(inv.name().equals(invCmp.name())&&inv.clazz().equals(invCmp.clazz())) {
				numInvGral=nInv+1;
				continue;
			}
		}
		if (numInvGral<0) {
			System.out.println("inv " + inv + " numInv<0 en searchNumInvII");
		}		
		return numInvGral;
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
	 * Prints structures for the calculation of probabilities of interference between invariants
	 */
	private void printMatProb() {
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
	private void printCAI() {
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
					for (MClassInvariant inv : lInvAttr) {
						System.out.println("      inv [" + inv.name() + "]");
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
	private void printMapInfoInv() {
		// Attributes & Assoc of Invariants
		System.out.println();
		System.out.println("============================================");
		System.out.println("Attributes & Assoc of Invariants");
		System.out.println("============================================");
		for (Map.Entry<MClassInvariant, InfoInv> entry : mapInfoInv.entrySet()) {
			MClassInvariant inv = entry.getKey();
			// Attributes & Assoc of Invariants
			System.out.println("inv [" + inv.name() + "]");
			List<MAttribute> lAttr = new ArrayList<MAttribute>();
			InfoInv oInfoInv = mapInfoInv.get(inv);
			// Attributes
			lAttr = oInfoInv.getlAttr();
			if (lAttr.size()>0) {
				for (MAttribute attr : lAttr) {
					System.out.println("     attr [" + attr.name() + "]");
				}				
			}
			// Assoc
			List<MAssociation> lAssoc = new ArrayList<MAssociation>();
			lAssoc = oInfoInv.getlAssoc();
			if (lAssoc.size()>0) {
				for (MAssociation assoc : lAssoc) {
					System.out.println("     assoc [" + assoc.name() + "]");
				}				
			}	
			System.out.println();
		}
		System.out.println("============================================");
		System.out.println("                *---*---*");
	}

	/**
	 * Print mapInfoAttr structure (invariants of an attribute)
	 */
	private void printMapInfoAttr(){
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
				System.out.println("     inv [" + inv.name() + "]");
			}
			System.out.println();
		}		
		System.out.println("============================================");
		System.out.println("                *---*---*");
	}

	/**
	 * Print mapInfoAssoc structure (invariants of an association)
	 */
	private void printMapInfoAssoc() {
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
				System.out.println("      inv [" + inv.name() + "]");
			}
			System.out.println();
		}	
		System.out.println("============================================");
		System.out.println("                *---*---*");
	}

	/**
	 * Algorithm 1 propose by Robert Clariso to find satisfiables combinations
	 * without using Solver
	 * @param col
	 * @return
	 */
	private List<MClassInvariant> greedyMethod(Collection<MClassInvariant> col){
		//	Preparation of Map of invariants with Set of invariants
		//	Un inv esta relacionado con otro porque utiliza atributos o asociaciones comunes

		List<MClassInvariant> result = new ArrayList<MClassInvariant>();

		// col -> Coleccion total de invariantes satisfiables

		// 1.	Inicialmente nuestra combinacion de invariantes esta vacia, y 
		//      el conjunto de invariantes posibles es { I -> col}. Invariants possibles

		Set<MClassInvariant> ic = new HashSet<MClassInvariant>(); // Invariants collection
		Set<MClassInvariant> ip = new HashSet<MClassInvariant>(); // Invariants possibles
		//		ip = col.; // Al principio, ip contiene todas las invariantes a tratar
		ip.addAll(col);
		boolean searchInv=true;
		while(searchInv) {
			if (ip.size()>0) searchInv=true;
			// Podemos buscar al azar entre los invariantes que previamente no se hayan usado
			// y hayan fallado.
			Set<MClassInvariant> ipRandom = new HashSet<MClassInvariant>();
			ipRandom.addAll(ip);
			ipRandom.removeAll(colInvFault);
			if (ipRandom.size()<=0) {
				searchInv=false;
			}
			if (searchInv) {
				// Convertimos Set en array para obtener elementos mas facilmente
				int n = ipRandom.size();		
				MClassInvariant arrInv[] = new MClassInvariant[n];
				arrInv = ipRandom.toArray(arrInv);			
				// 2.	Anyadimos a nuestra combinacion un invariante X 
				// elegida al azar dentro de { I -> ip}.

				Random random = new Random();
				int nRnd = random.nextInt(n);

				invXazar = arrInv[nRnd];
				ic.add(invXazar);

				// 3.	Eliminamos X de { I }.
				ip.remove(invXazar);

				// 4.	Consultamos los invariantes { Y } que tienen relacion 
				//      (acceden a algun elemento comun) con el invariante X. 
				Set<MClassInvariant> lInvY = new HashSet<MClassInvariant>();
				if (mapInfoInvSet.containsKey(invXazar)) {
					lInvY=mapInfoInvSet.get(invXazar);
					ip.removeAll(lInvY);
				}
			}
		}
		// el ic es el conjunto "maximo" de invariantes que no tienen elementos en comun
		result.addAll(ic);
		return result;

	}

	/**
	 * Print content of mapInfoInvSet
	 */
	private void printMapInfoInvSet() {
		System.out.println();
		System.out.println("Invariantes relacionadas entre si (mapInfoInvSet)");
		System.out.println();
		for (Map.Entry<MClassInvariant, Set<MClassInvariant>> entry : mapInfoInvSet.entrySet()) {
			MClassInvariant invKey = entry.getKey();
			System.out.println("Inv [" + invKey +"]");
			Set<MClassInvariant> lInvRrel = entry.getValue();
			for (MClassInvariant invRel: lInvRrel) {
				System.out.println("   * [" + invRel +"]");
			}
			System.out.println();
		}
		System.out.println("============================================");
		System.out.println("                *---*---*");
	}	

	/**
	 * Preparation structure to store invariants related to each invariant
	 */
	private void preparaMapInfoInvSet() {
		// Preparo Map de invariantes con Set de invariantes
		// Un inv esta relacionado con otro porque utiliza atributos o asociaciones comunes
		//		List<MClassInvariant> result = new ArrayList<MClassInvariant>();
		mapInfoInvSet.clear();
		for (Map.Entry<MClassInvariant, InfoInv> entry : mapInfoInv.entrySet()) {
			MClassInvariant invKey = entry.getKey();
			Set<MClassInvariant> lInvRel = new HashSet<MClassInvariant>();

			System.out.println("inv [" + invKey.name() + "]");
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
	}

	/**
	 * Search for groups of satisfiable combinations
	 */
	private void busca_grupos_SAT_MAX() {
		int maxCmb=0;
		mapGRP_SAT_MAX.clear();
		for (String combinacion: listSatisfiables) 
		{
			String[] strCmbs=combinacion.split("-");
			int nCmbs = strCmbs.length;
			// Buscar mayor numero de combinaciones a partir de 2 invariantes
			String strCmb=strCmbs[0];
			for (int nCmb = 1; nCmb < nCmbs; nCmb++) {
				if(!strCmb.equals("")) {
					strCmb+="-";
				}
				strCmb+=strCmbs[nCmb];
				String strValor="";
				int intValor;
				// Averiguar si dicha agrupacion ya existe y la acumula
				if (mapGRP_SAT_MAX.containsKey(strCmb)) {
					// Si esta usada, guardamos la key que la representa
					strValor=mapGRP_SAT_MAX.get(strCmb);
					intValor=Integer.parseInt(strValor)+1;
					if (intValor>maxCmb){
						maxCmb = intValor;
					}

					strValor = String.valueOf(intValor);
					mapGRP_SAT_MAX.put(strCmb, strValor);
				}else {
					// Si no esta usada, almacenamos con valor 'N' (Nueva)
					strValor="1";  
					if (maxCmb==0) {
						maxCmb=1;
					}
					mapGRP_SAT_MAX.put(strCmb, strValor);
				}
			}
		}

		HashMap<String, String> listRk = new HashMap<>();

		for (Map.Entry<String, String> entry : mapGRP_SAT_MAX.entrySet()) {
			String key = entry.getKey();
			String value = entry.getValue();
			int intValor=Integer.parseInt(value);
			int vrnk = maxCmb-intValor;
			String  strVrnk= String.valueOf(vrnk);

			String keyOrdenada = strVrnk + " - " + key;
			if (listRk.containsKey(keyOrdenada)) {
				listRk.put(keyOrdenada, value);
			}else {
				listRk.put(keyOrdenada, value);
			}
		}
	}

	/**
	 * Sort combinations
	 * @param listSorted
	 * @param numInvs
	 * @return
	 */
	private List<String> sortByCmbNumber(List<String> listSorted, int numInvs) {
		List<String> listRes = new ArrayList<>();

		HashMap<String, String> listRk = new HashMap<>();
		for (String strCmb: listSorted) {
			int nGrupos = numInvs - (strCmb.length()-strCmb.replace("-","").length())+1;

			// Hallar Key que le corresponde si ordenamos sus partes
			String keyOrdenada = nGrupos + " " + strCmb;
			String valor="";
			// Averiguar si dicha Key ya esta usada anteriormente
			if (listRk.containsKey(keyOrdenada)) {
				// Si esta usada, guardamos la key que la representa
				valor=strCmb;
				listRk.put(keyOrdenada, valor);
			}else {
				// Si no esta usada, almacenamos con valor 'N' (Nueva)
				valor="N";  
				listRk.put(keyOrdenada, valor);
			}

		}
		listRes = new ArrayList<>(listRk.keySet());
		Collections.sort(listRes);
		List<String> listResLimpia = new ArrayList<>();
		for (String strCmb: listRes) {
			String valor=strCmb.split(" ")[1];
			listResLimpia.add(valor);
		}
		return listResLimpia;
	}

	/**
	 * Show list of invariants 
	 * @param invClassSatisfiables
	 * @param invClassUnSatisfiables
	 * @param invClassOthers
	 */
	private void showResult(Collection<IInvariant> invClassSatisfiables, 
			Collection<IInvariant> invClassUnSatisfiables,
			Collection<IInvariant> invClassOthers) {
		System.out.println();
		System.out.println("MVM: SATISFIABLES en showResult");
		for (IInvariant invClass: invClassSatisfiables) {
			int orden=-1;
			String strNameInv = invClass.clazz().name()+"::"+invClass.name();
			if (mapInvRes.containsKey(strNameInv)) {
				ResInv invRes = (ResInv) mapInvRes.get(strNameInv);
				orden=invRes.intOrden;
			}
			System.out.println("MVM: " + orden + " " + strNameInv);
		}
		System.out.println();
		System.out.println("MVM: UNSATISFIABLES");
		for (IInvariant invClass: invClassUnSatisfiables) {
			int orden=-1;
			String strNameInv = invClass.clazz().name()+"::"+invClass.name();
			if (mapInvRes.containsKey(strNameInv)) {
				ResInv invRes = (ResInv) mapInvRes.get(strNameInv);
				orden=invRes.intOrden;
			}
			System.out.println("MVM: " + orden + " " + strNameInv);
		}

		if(invClassOthers.size()>0) {
			System.out.println();
			System.out.println("MVM: OTHERS");
			for (IInvariant invClass: invClassOthers) {
				System.out.println("MVM: " + invClass.name());
			}
		}
		System.out.println("============================================");
		System.out.println("                *---*---*");
	}

	/**
	 * Shows overall result 
	 */
	private void showResultGral() {
		System.out.println();
		System.out.println("MVM: SATISFIABLES ["+ listSatisfiables.size()+"]");
		if(listSatisfiables.size()>0 && showSatisfiables) {			
			for (String cmbSatisfiable: listSatisfiables) {
				System.out.println("MVM: " + cmbSatisfiable);
			}
		}
		System.out.println();
		System.out.println("MVM: UNSATISFIABLES ["+ listUnSatisfiables.size()+"]");
		if(listUnSatisfiables.size()>0 && showUnsatisfiables) {			
			for (String cmbUnSatisfiable: listUnSatisfiables) {
				System.out.println("MVM: " + cmbUnSatisfiable);
			}
		}

		if(listOthers.size()>0) {
			System.out.println();
			System.out.println("MVM: OTHERS ["+ listOthers.size()+"]");
			if(listOthers.size()>0 && showOthers) {	
				for (String cmbOther: listOthers) {
					System.out.println("MVM: " + cmbOther);
				}
			}
		}

		if(listCmbRes.size()>0 && showSummarizeResults) {
			int nCmb=0;
			int nCmbs=listCmbRes.size();
			System.out.println();
			System.out.println("MVM: calculation summary ["+ nCmbs+"]");
			int lenCmb = ((ResComb) listCmbRes.get(0)).combinacion.length()+2;

			System.out.println("=============================================================================================");

			for (ResComb cmbRes: listCmbRes) {
				nCmb+=1;
				String linea = "";
				linea= String.format(nCmb + " de " + nCmbs + " "+ "%-"+lenCmb+"s",cmbRes.combinacion);
				linea+=" "+String.format("%-15s",cmbRes.resultado);
				linea+=" "+String.format("%-25s",cmbRes.comentario);
				System.out.println("MVM: " + linea);
			}
			System.out.println();
		}
		System.out.println("MVM: llamadas a Solver: " + numCallSolver);
		System.out.println("============================================");
		System.out.println("                *---*---*");
	}

	/**
	 * Get all possible combinations
	 * @param invariantes to mix
	 */
	public  void mixInvariants(Map<Integer, IInvariant> samples) {
		//		int nInvs = samples.size();
		// extend("", 1, nInvs); // Antes
		int nInvs = invClassTotal.size();
		if (debMVM) {
			System.out.println("\nInvariants to treat: (" + nInvs + ")");
			System.out.println("----------------------------");

			int nTrata = 0;
			for (Entry<Integer, IInvariant> obj : samples.entrySet()) 
			{
				nTrata = obj.getKey();
				String nameInv = obj.getValue().name();

				System.out.println("MVM: a tratar " +nTrata+" " + nameInv);

			}

			System.out.println("============================================");
			System.out.println("                *---*---*");
		}
		// Desarrolla combinaciones desde un nivel (1) a otro (nInvs)
		extend("", 1, nInvs); 
	}

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
	public static void extend(String base, int nivIni, int nivMax) {
		for (int nInv = nivIni; nInv < nivMax+1; nInv++) {

			// kinv sera la clave de samples segun la posicion indicada por nInv 
			// Buscar siempre que nInv no sea unsatisfiable desde el primer momento

			// Comprobar si esta en lista de unsatisfiable (nInv+1 formateada)
			//Aqui9
			String strNinvCmp = String.format("%0"+String.valueOf(nivMax).length()+"d",nInv);
			boolean isUnsatisfiable=false;

			if (listUnSatisfiables.contains(strNinvCmp)) {
				isUnsatisfiable=true;
			}
			if (!isUnsatisfiable) {
				Integer kInv = getKeyElement(samples, nInv);
				if (samples.containsKey(nInv)) {// OJO
					kInv=nInv;


					// Si nInv no esta en baseIn se guarda y se extendiende

					String[] partes = base.split("-");
					boolean guardar=true;
					for (int i = 0 ; i < partes.length ; i++) {
						String descParte = partes[i].trim();
						String strNinv = String.format("%0"+String.valueOf(nivMax).length()+"d",kInv);
						if (descParte.equals(strNinv)) {
							guardar=false;
							i=partes.length;
						}
					}
					if (guardar) {
						String cmb=base;
						String strNinv = String.format("%0"+String.valueOf(nivMax).length()+"d",kInv);
						if (!cmb.equals("")) {
							cmb+="-";
						}
						cmb+=strNinv;
						storeResult(cmb);
						if (nInv<nivMax) {
							extend(cmb, nInv+1, nivMax); 
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
			if (debMVM) {
				System.out.println("Encuentra " + keyOrdenada + " y guarda "+combination);
			}
		}else {
			// Si no esta usada, almacenamos con valor 'N' (Nueva)
			valor="N";  
			listCmb.put(keyOrdenada, valor);
			listCmbSel.put(keyOrdenada, combination);
		}
	}

	public static void storeResultCmb(String combination, String resultado, String comentario) {
		ResComb res = new ResComb(combination, resultado, comentario);
		if (!listCmbRes.contains(res)) {
			listCmbRes.add(res);
		}
	}

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
	public void sendToValidate(List<String> listSorted , Collection<IInvariant> invClassTotal) {

		int cmbSel = listCmbSel.size();
		int acumVal=0;
		//		int acumTrata=0;
		if (debMVM) {
			String head="Send to Validator ("+ listSorted+") combinations. (listSorted)";
			System.out.println(head);
			System.out.println(("-").repeat(head.length()));
		}
		KodkodSolver kodkodSolver = new KodkodSolver();
		List<IInvariant> listInv = new ArrayList<IInvariant>();

		try {
			for (String combinacion: listSorted) 
			{
				//System.out.println("MVM: Bucle pral de sendToValidate (" + combinacion + ")");
				boolean calculate=true;
				// Ver si la combinacion se halla incluida en una satisfactible
				// Si la combinacion esta incluida en alguna combinacion satisfactible
				// no hace falta calcularla porque tambien sera satisfactible
				calculate = !includedInSatisfactible(combinacion);

				if (calculate) {
					// Ver si hay combinaciones insatisfactibles que esten incluidas en la combinacion a tratar
					// Si la combinacion a tratar contiene una combinacion insatisfactible, sera insatisfactible
					calculate = !unsatisIncludedInCombination( combinacion);
				}

				if (calculate) {
					// Buscar invariantes de la combinacion
					listInv=splitInvCombination( combinacion);
					Solution solution=null;
					try {
						solution = calcular( combinacion,  invClassTotal,  kodkodSolver);

					} catch (Exception e) {
						e.printStackTrace();
					}
					acumVal+=1;
					String resultado = cmbSel + " (" + acumVal+ ") " + String.format("%-20s",combinacion);
					resultado += " - ["+ solution.outcome()+"]";
					//										if (debMVM) {
					System.out.println("MVM: " + resultado);
					//										}
					if (solution.outcome().toString() == "SATISFIABLE") {
						listSatisfiables.add(combinacion);
						storeResultCmb(combinacion, "SATISFIABLE", "Direct calculation");
					}else if (solution.outcome().toString() == "UNSATISFIABLE") {
						listUnSatisfiables.add(combinacion);
						storeResultCmb(combinacion, "UNSATISFIABLE", "Direct calculation");
						// Si fuese insatisfactible, valdria la pena hallar los unsatisfactibles cores
						calcularRec(combinacion, invClassTotal,  kodkodSolver, acumVal);
					} else {
						listOthers.add(combinacion);
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public Solution calcular(String combinacion, Collection<IInvariant> invClassTotal, KodkodSolver kodkodSolver) {
		if (debMVM) {
			System.out.println("MVM: Entra en calcular (" + combinacion + ")");
		}
		Solution solution=null;
		// Buscar invariantes de la combinacion
		List<IInvariant> listInv = new ArrayList<IInvariant>();
		listInv=splitInvCombination( combinacion);
		int numInvs = listInv.size();

		// Activar solo las de la combinacion
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

	private void calcularRec(String combinacion, Collection<IInvariant> invClassTotal, KodkodSolver kodkodSolver, int acumVal) {
		if (debMVM) {
			System.out.println("MVM: Entra en calcularRec (" + combinacion + ")");
		}
		// Si una combinacion es Unsat, hay que buscar el core unsat activando todas menos 1 y clasificarla
		// Por ejemplo, si 1-2-3-5 es unsat, hemos de probar:
		// 1-2-3
		// 1-2-5
		// 1-3-5
		// 2-3-5
		// Si es sat, se anyade a listSatisfiables y ya esta
		// Si es unsat, se anyade a listUnSatisfiables y de nuevo se envia a calcularRec
		//...
		int cmbSel = listCmbSel.size();
		String[] invs = combinacion.split("-");	
		int nCmbs = invs.length;

		// Se fabrican tantas combinaciones como invariantes hayan pero eliminando una
		for (int nCmb = 0; nCmb < nCmbs; nCmb++) {
			String newCmb = "";
			for (int nCmbW = 0; nCmbW < nCmbs; nCmbW++) {
				if (nCmbW!=nCmb) {
					if (!newCmb.equals("")) {
						newCmb+="-";
					}
					newCmb+=invs[nCmbW];
				}
			}

			boolean calculate=true;
			calculate = !includedInSatisfactible(newCmb);

			if (calculate) {
				// Ver si hay combinaciones insatisfactibles que esten incluidas en la combinacion a tratar
				calculate = !unsatisIncludedInCombination( newCmb);
			}

			if (calculate) {
				Solution solution = null;
				try {
					solution = calcular( newCmb,  invClassTotal,  kodkodSolver);
				} catch (Exception e) {
					e.printStackTrace();
				}
				acumVal+=1;

				String resultado = cmbSel + " " + acumVal+ " " + String.format("%-20s",newCmb);
				resultado += " - ["+ solution.outcome()+"]";
				if (debMVM) {
					System.out.println("MVM - calcularRec: " + resultado);
				}
				if (solution.outcome().toString() == "SATISFIABLE") {
					listSatisfiables.add(newCmb);
					storeResultCmb(newCmb, "SATISFIABLE", "Direct calculation");
				}else if (solution.outcome().toString() == "UNSATISFIABLE") {
					listUnSatisfiables.add(newCmb);
					storeResultCmb(newCmb, "UNSATISFIABLE", "Direct calculation");
					// Si fuese insatisfactible, valdria la pena hallar los unsatisfactibles cores
					//...
					calcularRec(newCmb, invClassTotal,  kodkodSolver, acumVal);
				} else {
					listOthers.add(newCmb);
				}
			}

		}
	}

	/**
	 * Buscar invariantes de la combinacion
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
			if (samples.containsKey(invID)) {
				IInvariant inv = (IInvariant) samples.get(invID);
				listInvW.add(inv);				
			}
		}
		return listInvW;
	}

	/**
	 * Chek if combinations existe in listSatisfiables list
	 * @param combinacion
	 * @return
	 */

	private boolean includedInSatisfactible(String combinacion) {
		//System.out.println("Combinacion "+combinacion);
		boolean bRes=false;

		// Partes de la combinacion a valorar

		String[] aCmbTratar = combinacion.split("-");	

		for (String cmbSatisfiable: listSatisfiables) {

			// Invariantes de cada combinacion satisfactible
			String[] aCmbSat = cmbSatisfiable.split("-");	

			List<String> lCmbSat=new ArrayList<String>();
			Collections.addAll(lCmbSat, aCmbSat);
			boolean todasExisten=true;
			for (int nCmb=0;nCmb<aCmbTratar.length;nCmb++) {
				String parte = aCmbTratar[nCmb];
				// Si una parte de la combinacion a tratar no existe hay que tratar la combinacion
				if (!lCmbSat.contains(parte)) {
					todasExisten=false;
					nCmb=aCmbTratar.length;
					continue;
				}
			}
			if (todasExisten) {
				storeResultCmb(combinacion, "SATISFIABLE", "Indirect calculation. Already exists in combination ("+cmbSatisfiable+")");
				if (!listSatisfiables.contains(combinacion)) {
					listSatisfiables.add(combinacion);// OJO JG 1
				}
				return true;
			}
		}

		return bRes;
	}

	/**
	 * Si hay alguna combinacion unsatisfactible contenida en la combinacion a tratar, diremos que la 
	 * combinacion tambien es insatisfactible
	 * @param combinacion
	 * @return
	 */

	private boolean unsatisIncludedInCombination(String combinacion) {

		boolean bRes=false;

		// Partes de la combinacion a valorar

		String[] aCmbTratar = combinacion.split("-");	
		List<String> lCmbATratar=new ArrayList<String>();
		Collections.addAll(lCmbATratar, aCmbTratar);

		for (String cmbUnSatisfiable: listUnSatisfiables) {

			// Partes de cada combinacion unsatisfactible
			String[] aCmbUnSat = cmbUnSatisfiable.split("-");	

			boolean todasExisten=true;
			for (int nCmb=0;nCmb<aCmbUnSat.length;nCmb++) {
				String parte = aCmbUnSat[nCmb];
				// Si una parte de la combinacion a tratar no existe hay que tratar la combinacion

				if (!lCmbATratar.contains(parte)) {
					todasExisten=false;
					nCmb=aCmbUnSat.length;
					continue;
				}
			}
			if (todasExisten) {
				storeResultCmb(combinacion, "UNSATISFIABLE", "Indirect calculation. Contains ("+cmbUnSatisfiable+")");
				if (!listUnSatisfiables.contains(combinacion)) {
					listUnSatisfiables.add(combinacion);// OJO JG 1
				}
				return true;
			}
		}

		return bRes;
	}

	/**
	 * 
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
 * Clase destinada a almacenar el resultado y comentario de cada combinacion
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

class KeyClassAttrOld {
	String nomClase;
	String nomAttr;
	public KeyClassAttrOld(String vNomClase, String vNomAttr) {
		this.nomClase = vNomClase;
		this.nomAttr = vNomAttr;
	}
}



