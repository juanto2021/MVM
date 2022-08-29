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

	public static Collection<IInvariant> invClassTotal = new ArrayList<IInvariant>();

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
	private static String fmt="";

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

	public static Map<Integer, IInvariant> samples = new HashMap<>();	

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
		samples.clear();
		colInvFault.clear();

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
			tabInvMClass = new MClassInvariant[invClassTotal.size()];	
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
			if (debMVM) {
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
		String tipoSearchMSS="L";
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
						numCallSolverUNSAT,
						tipoSearchMSS);
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
		fmt = "%0"+String.valueOf(invClassTotal.size()).length()+"d";

		// In this point We must to treat only the invariants that are satisfiables alone
		// Make col collection and strCmbTotal
		Collection<MClassInvariant> col = new ArrayList<MClassInvariant>();
		col = makeCollectionInvs(invClassSatisfiables);
		String strCmbTotal = makeTotalCmb(col);
		strCmbTotal= sortCmb(strCmbTotal);

		// Here We have a collection of MClassInvariant all them satisfiables
		buildTreeVisitor(col);

		// Preparation of Map of invariants with Set of invariants
		// Un inv esta relacionado con otro porque utiliza atributos o asociaciones comunes
		preparaMapInfoInvSet();

		// Prepara tabla atributos comunes por cada pareja de invariantes
		preparaProbMat(mModel.classInvariants());

		// Muestra estructuras resultantes del Visitor
		if (showStructuresAO) {
			printStructuresAO();
		}

		// Calcula una combinacion base segun metodo Greedy
		List<String> resGreedy = new ArrayList<String>();
		String strCmbBase ="";
		// modeG = "R", se usa random para empezar por una invariante
		// modeG = "T" se usan todas las invariantes para unir resultados
		String modeG="T";// Get the best results

		int iIni, iFin;
		if (modeG.equals("R")) {
			iIni=0;
			iFin=1;
		}else {
			iIni=0;
			iFin=col.size();	
		}
		for(int nInv=iIni;nInv<iFin;nInv++) {
			int nInvTratar=nInv;
			strCmbBase = bucleGreedy(modeG, col, nInvTratar);
			resGreedy.add(strCmbBase);
		}

		for(String strCmbGreedy:resGreedy) {
			strCmbBase = strCmbGreedy;
			String strCmbResto = makeRestCmb(strCmbBase, strCmbTotal);

			List<String> resGral = new ArrayList<String>();
			List<String> resSat = new ArrayList<String>();
			resGral.add(strCmbBase);
			String newResto=strCmbResto;
			while(newResto!="") {
				String[] aInvsResto=newResto.split("-");
				int nInvsR = aInvsResto.length;		
				newResto="";
				resSat.clear();
				for (String cmbA: resGral) {
					for(int nInvR = 0;nInvR<nInvsR;nInvR++) {
						String invR = aInvsResto[nInvR];
						invR = String.format(fmt,Integer.parseInt(invR));
						// si invR esta dentro de cmbA no se guarda
						boolean guardar=true;
						String[] aInvsA=cmbA.split("-");
						int nInvsA = aInvsA.length;	
						for(int nInvA = 0;nInvA<nInvsA;nInvA++) {
							String pA = aInvsA[nInvA];
							if (pA.equals(invR)) {
								guardar=false;
								continue;
							}
						}
						if (guardar) {
							String newCmb = cmbA + "-" + invR;
							newCmb=sortCmb(newCmb);
							if (!resSat.contains(newCmb)) {
								System.out.println("newCmb [" + newCmb + "]");
								String solucion="";
								solucion = calcularGreedy( newCmb,  invClassTotal);
								if (solucion=="SATISFIABLE") {
									addSolutionG(newCmb, solucion);
									resSat.add(newCmb);
									if (newResto!="") {
										newResto+="-";
									}
									newResto+=invR;
								}else {
									// Buscar por parejas
									String[] aInvsB=cmbA.split("-");
									int nInvsB = aInvsB.length;
									for (int nInvB = 1;nInvB<=nInvsB;nInvB++) {
										String invB=aInvsB[nInvB-1];
										String cmbMUS=invB + "-" + invR;
										cmbMUS = sortCmb(cmbMUS) ;
										if (listSatisfiables.contains(cmbMUS)||listUnSatisfiables.contains(cmbMUS)) {
											continue;
										}
										solucion = calcularGreedy( cmbMUS,  invClassTotal);
										addSolutionG(cmbMUS, solucion);
										System.out.println("cbmProbe [" + cmbMUS + "] solution " + solucion);
									}
								}
							}
						}
					}
				}
				resGral.clear();
				for (String cmb:resSat) {
					resGral.add(cmb);
				}	
			}
			// -- Provis Ini
			listSatisfiables = sortByNumInv(listSatisfiables,"D");
			int hay = listSatisfiables.size();
			if (hay>3) hay=5;
			for (int j=0;j<hay;j++) {
				String cmbSat = listSatisfiables.get(j);
				System.out.println("strCmbBase ["+ strCmbBase +"] Sat ["+cmbSat+"]");
			}
			System.out.println("Fin bucle");
			// -- Provis Fin
		}


		if (bShowResultGral) showResultGral();
		Instant end = Instant.now();
		Duration timeElapsed = Duration.between(start, end);
		LOG.info("MVM: Time taken: "+ timeElapsed.toMillis() +" milliseconds");

		String tipoSearchMSS="G";
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
						numCallSolverUNSAT,
						tipoSearchMSS);
	}
	/**
	 * Loop to be able to call Greedy randomly or for each invariant
	 * @param modeG
	 * @param col
	 * @param iTratar
	 * @return
	 */
	private String bucleGreedy(String modeG, Collection<MClassInvariant> col, int iTratar) {
		String strCmbBase="";
		List<MClassInvariant> ic = new ArrayList<MClassInvariant>();
		colInvFault.clear();
		boolean useGreedy=true;
		while (useGreedy) {
			// Calculate the combination obtained in greedyMethod

			listCmb.clear();
			listCmbRes.clear();
			List<String> listSorted = new ArrayList<String>();
			// ic es la lista de combinaciones que no tienen nada en comun
			ic = greedyMethod(modeG, col, iTratar);				
			System.out.println("Invariants collection (ic): " + ic.size());
			String strCmb="";
			strCmbBase ="";
			for (MClassInvariant inv:ic) {
				int nCmb = searchNumInv(inv);
				if (nCmb>0) {
					if (!strCmb.equals("")) {
						strCmb=strCmb+"-";
					}
					String strNinv = String.format(fmt,nCmb);
					strCmb=strCmb+strNinv;
					strCmb = sortCombination( strCmb); 
					storeResult(strCmb);
				}
			}

			strCmbBase= sortCmb(strCmb);
			String solucion="";
			LOG.info("MVM: Envio a calcularGreedy.");
			solucion = calcularGreedy( strCmbBase,  invClassTotal);	
			addSolutionG(strCmbBase, solucion);
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
		return strCmbBase;
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
	private static int searchNumInvII(IInvariant inv) {
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
	private static void printMapInfoInv() {
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
	private List<MClassInvariant> greedyMethod(String modeG, Collection<MClassInvariant> col, int nInvTratar){
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
		boolean pVez=true;
		boolean searchInv=true;
		while(searchInv) {
			if (ip.size()>0) searchInv=true;
			// Podemos buscar al azar entre los invariantes que previamente no se hayan usado
			// y hayan fallado.
			Set<MClassInvariant> ipRandom = new HashSet<MClassInvariant>();
			ipRandom.addAll(ip);
			ipRandom.removeAll(colInvFault);// Se eliminan las que hayan podido fallar anteriormente
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

				if (modeG.equals("R")) {
					Random random = new Random();
					int nRnd = random.nextInt(n);
					invXazar = arrInv[nRnd];
				}else {
					if (pVez) {
						invXazar = arrInv[nInvTratar];
						pVez=false;
					}else {
						invXazar = arrInv[0];
					}
				}
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
	 * Ordena invariantes de menor a mayor formateando con 0 por la izquierda
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
	private static String makeTotalCmb(Collection<MClassInvariant> col) {
		String strCmbTotal="";
		for (MClassInvariant invClass: col) {
			int nCmb = searchNumInv(invClass);
			String strNinv = String.format(fmt,nCmb);
			if (strCmbTotal!="") {
				strCmbTotal+="-";
			}
			strCmbTotal+=strNinv;	
		}
		return strCmbTotal;
	}

	/**
	 * Given a base combination obtained with greedy, look for relation of invariants
	 * remaining and returns a combination with all of them
	 * @param strCmbBase
	 * @param strCmbTotal
	 * @return
	 */
	private static String makeRestCmb(String strCmbBase, String strCmbTotal) {
		List<String> listRes = new ArrayList<String>();
		strCmbBase=sortCmb(strCmbBase);
		strCmbTotal=sortCmb(strCmbTotal);
		String resCmb="";
		String[] aInvsBase=strCmbBase.split("-");
		int nInvsBase = aInvsBase.length;
		String[] aInvsTotal=strCmbTotal.split("-");
		int nInvsTotal = aInvsTotal.length;		
		for(int nInvTotal = 0;nInvTotal<nInvsTotal;nInvTotal++) {
			boolean halla=false;
			String invTotal = aInvsTotal[nInvTotal];
			for(int nInvBase = 0;nInvBase<nInvsBase;nInvBase++) {
				String invBase = aInvsBase[nInvBase];
				if (invBase.equals(invTotal)) {
					halla=true;
					continue;
				}
			}
			if (!halla) {
				listRes.add(invTotal);
			}
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
	 * Find all combinations of a group of invariants
	 * @param strCmb
	 * @return
	 */
	private static List<String> combines(String strCmb) {
		fmt = "%0"+String.valueOf(invClassTotal.size()).length()+"d";
		List<String> resGral = new ArrayList<String>();
		String[] aInvs=strCmb.split("-");
		int nInvs = aInvs.length;
		for (int nInv = 1;nInv<=nInvs;nInv++) {
			String inv = aInvs[nInv-1];
			String invF1 = String.format(fmt,Integer.parseInt(inv));
			String cmb = invF1;
			if (!resGral.contains(cmb)) {
				resGral.add(cmb);
				if (debMVM) System.out.println("Incluyo en resGral[" + cmb + "]");
			}
			int nCmbs = resGral.size();
			for (int nCmb = 0;nCmb<nCmbs;nCmb++) {
				String cmbR = resGral.get(nCmb);
				if (cmbR!=invF1) {
					String newCmb = cmbR + "-" + invF1;
					if (!resGral.contains(newCmb)) {
						resGral.add(newCmb);
						if (debMVM) System.out.println("Incluyo en resGral[" + newCmb + "]");
					}
				}
			}
		}		
		Collections.sort(resGral);
		return resGral;
	}	
	/**
	 * Sort list of invariants by placing on the first element
	 * the combination with more invariants and so on
	 * @param listCmb
	 * @return
	 */
	private static List<String> sortByNumInv(List<String> listCmb, String typeSort) {
		int nOrdenMax = 100000;
		String fmtG = "%06d";	
		List<String> listWork = new ArrayList<String>();
		List<String> listRes = new ArrayList<String>();
		for (String strCmb: listCmb) {
			String[] aInvs=strCmb.split("-");
			int nInvs = aInvs.length;
			int nOrden = 0;
			if (typeSort == "D") {
				nOrden = nOrdenMax-nInvs;
			}else {
				nOrden = nInvs;
			}
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
	/**
	 * Print content of mapInfoInvSet
	 */
	private static void printMapInfoInvSet() {
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
	private static void preparaMapInfoInvSet() {
		// Preparo Map de invariantes con Set de invariantes
		// Un inv esta relacionado con otro porque utiliza atributos o asociaciones comunes
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
			// Find the greatest number of combinations from 2 invariants
			String strCmb=strCmbs[0];
			for (int nCmb = 1; nCmb < nCmbs; nCmb++) {
				if(!strCmb.equals("")) {
					strCmb+="-";
				}
				strCmb+=strCmbs[nCmb];
				String strValor="";
				int intValor;
				// Find out if said group already exists and accumulates it
				if (mapGRP_SAT_MAX.containsKey(strCmb)) {
					// If it is used, we save the key that represents it
					strValor=mapGRP_SAT_MAX.get(strCmb);
					intValor=Integer.parseInt(strValor)+1;
					if (intValor>maxCmb){
						maxCmb = intValor;
					}

					strValor = String.valueOf(intValor);
					mapGRP_SAT_MAX.put(strCmb, strValor);
				}else {
					// If it is not used, we store with value 'N' (New)
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
			int nGrupos = numInvs - (strCmb.length()-strCmb.replace("-","").length()+1);// no se
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
	public static void extend(String base, int nivIni, int nivMax) {
		for (int nInv = nivIni; nInv < nivMax+1; nInv++) {

			// kinv sera la clave de samples segun la posicion indicada por nInv 
			// Buscar siempre que nInv no sea unsatisfiable desde el primer momento

			// Comprobar si esta en lista de unsatisfiable (nInv+1 formateada)
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
	/**
	 * Stores comment of a combination
	 * @param combination
	 * @param resultado
	 * @param comentario
	 */
	public static void storeResultCmb(String combination, String resultado, String comentario) {
		ResComb res = new ResComb(combination, resultado, comentario);
		if (!listCmbRes.contains(res)) {
			listCmbRes.add(res);
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
	public void sendToValidate(List<String> listSorted , Collection<IInvariant> invClassTotal) {

		int cmbSel = listCmbSel.size();
		int acumVal=0;

		if (debMVM) {
			String head="Send to Validator ("+ listSorted+") combinations. (listSorted)";
			System.out.println(head);
			System.out.println(("-").repeat(head.length()));
		}
		KodkodSolver kodkodSolver = new KodkodSolver();

		try {
			for (String combinacion: listSorted) 
			{
				boolean calculate=true;
				// See if the combination is included in a satisfiable
				// If the join is included in some satisfiable join
				// there is no need to calculate it because it will also be satisfiable
				calculate = !includedInSatisfactible(combinacion);
				if (calculate) {
					// See if there are unsatisfiable joins that are included in the join to try 
					// If the join to try contains an unsatisfiable join, it will be unsatisfiable
					calculate = !unsatisIncludedInCombination( combinacion);
				}

				if (calculate) {
					// Find invariants of the combination
					String solucion="";
					//					Solution solution=null;
					try {
						//						solution = calcular( combinacion,  invClassTotal);
						solucion = calcularGreedy( combinacion,  invClassTotal);
					} catch (Exception e) {
						e.printStackTrace();
					}
					acumVal+=1;
					String resultado = cmbSel + " (" + acumVal+ ") " + String.format("%-20s",combinacion);
					resultado += " - ["+ solucion+"]";
					// Aqui poner if (debMVM)
					if (debMVM) {
						System.out.println("MVM: " + resultado);
					}
					addSolutionG(combinacion, solucion);
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
	public void addSolution(String combinacion, Solution solution) {
		if (solution.outcome().toString() == "SATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_SATISFIABLE") {
			if (!listSatisfiables.contains(combinacion)) {
				listSatisfiables.add(combinacion);
			}				
			storeResultCmb(combinacion, "SATISFIABLE", "Direct calculation");
		}else if (solution.outcome().toString() == "UNSATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_UNSATISFIABLE") {
			if (!listUnSatisfiables.contains(combinacion)) {
				listUnSatisfiables.add(combinacion);
			}			
			storeResultCmb(combinacion, "UNSATISFIABLE", "Direct calculation");
		} else {
			listOthers.add(combinacion);
		}
	}
	/**
	 * Add solution of a combination to the list of Satisfiables or Unsatisfiables (especial para Greedy)
	 * @param combinacion
	 * @param solution
	 */
	public void addSolutionG(String combinacion, String solucion) {
		if (solucion.equals("SATISFIABLE") || solucion.equals("TRIVIALLY_SATISFIABLE")) {
			//			listSatisfiables.add(combinacion);
			if (!listSatisfiables.contains(combinacion)) {
				listSatisfiables.add(combinacion);
				storeResultCmb(combinacion, "SATISFIABLE", "Direct calculation");
			}							

		}else if (solucion.equals("UNSATISFIABLE") || solucion.equals("TRIVIALLY_UNSATISFIABLE")) {
			if (!listUnSatisfiables.contains(combinacion)) {
				listUnSatisfiables.add(combinacion);
				storeResultCmb(combinacion, "UNSATISFIABLE", "Direct calculation");
			}
		} else {
			listOthers.add(combinacion);
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
			System.out.println("MVM: Entra en calcular (" + combinacion + ")");
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
	public String calcularGreedy(String combinacion, Collection<IInvariant> invClassTotal) {
		KodkodSolver kodkodSolver = new KodkodSolver();
		String solucion="";
		if (debMVM) {
			System.out.println("MVM: Entra en calcular (" + combinacion + ")");
		}
		// First of all see if you can deduce the result
		boolean calculate=true;
		// See if the combination is included in a satisfiable
		// If the join is included in some satisfiable join
		// there is no need to calculate it because it will also be satisfiable	
		calculate = !includedInSatisfactible(combinacion);
		if (!calculate) {
			solucion="SATISFIABLE";
			return solucion;
		}
		if (calculate) {
			// See if there are unsatisfiable joins that are included in the join to try 
			// If the join to try contains an unsatisfiable join, it will be unsatisfiable
			calculate = !unsatisIncludedInCombination( combinacion);
			if (!calculate) {
				solucion="UNSATISFIABLE";
				return solucion;
			}
		}
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
	 * Old method of calculation
	 * @param combinacion
	 * @param invClassTotal
	 * @param kodkodSolver
	 * @return
	 */
	public Solution calcularOld(String combinacion, Collection<IInvariant> invClassTotal, KodkodSolver kodkodSolver) {

		if (debMVM) {
			System.out.println("MVM: Entra en calcular (" + combinacion + ")");
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
				// do nothing
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		return solution;
	}
	/**
	 * Recursive calculus (deprecated)
	 * @param combinacion
	 * @param invClassTotal
	 * @param kodkodSolver
	 * @param acumVal
	 */
	private void calcularRec(String combinacion, Collection<IInvariant> invClassTotal, KodkodSolver kodkodSolver, int acumVal) {
		if (debMVM) {
			System.out.println("MVM: Entra en calcularRec (" + combinacion + ")");
		}
		// If a combination is Unsat, find the unsat core by activating all but 1 and classify it
		// For example, if 1-2-3-5 is unsat, we have to test:
		// 1-2-3
		// 1-2-5
		// 1-3-5
		// 2-3-5
		// If it is sat, it is added to listSatisfiables and that's it
		// If it is unsat, it is added to listUnSatisfiables and sent again to calculateRec
		//...
		int cmbSel = listCmbSel.size();
		List<String> lisWork = new ArrayList<String>();
		lisWork = combines(combinacion);
		lisWork = sortByNumInv(lisWork,"D");
		int nCmbs=lisWork.size();
		// As many combinations as there are invariants are made in search of MUS
		for (int nCmb = 0; nCmb < nCmbs; nCmb++) {
			String newCmb = lisWork.get(nCmb);
			if (newCmb.equals(combinacion)) {
				continue;
			}
			boolean calculate=true;
			calculate = !includedInSatisfactible(newCmb);

			if (calculate) {
				// See if there are unsatisfiable combinations that are included in the combination to be treated
				calculate = !unsatisIncludedInCombination( newCmb);
			}

			if (calculate) {
				Solution solution = null;
				try {
					solution = calcular( newCmb,  invClassTotal);
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
					// If it were unsatisfiable, would it be worth finding the unsatisfiable cores?
					//...
					calcularRec(newCmb, invClassTotal,  kodkodSolver, acumVal);
				} else {
					listOthers.add(newCmb);
				}
			}
		}
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

	/**
	 * Chek if combinations exist in listSatisfiables list
	 * @param combinacion
	 * @return
	 */

	private boolean includedInSatisfactible(String combinacion) {
		boolean bRes=false;

		// Parts of the combination to be valued

		String[] aCmbTratar = combinacion.split("-");	

		for (String cmbSatisfiable: listSatisfiables) {

			// Invariants of each satisfiable combination
			String[] aCmbSat = cmbSatisfiable.split("-");	

			List<String> lCmbSat=new ArrayList<String>();
			Collections.addAll(lCmbSat, aCmbSat);
			boolean todasExisten=true;
			for (int nCmb=0;nCmb<aCmbTratar.length;nCmb++) {
				String parte = aCmbTratar[nCmb];
				// If a part of the combination to be treated does not exist, the combination must be treated
				if (!lCmbSat.contains(parte)) {
					todasExisten=false;
					nCmb=aCmbTratar.length;
					continue;
				}
			}
			if (todasExisten) {
				storeResultCmb(combinacion, "SATISFIABLE", "Indirect calculation. Already exists in combination ("+cmbSatisfiable+")");
				if (!listSatisfiables.contains(combinacion)) {
					listSatisfiables.add(combinacion);
				}
				return true;
			}
		}
		return bRes;
	}

	/**
	 * If there is some unsatisfiable combination contained in the combination to be treated, we will say that the
	 * combination is also unsatisfiable
	 * @param combinacion
	 * @return
	 */

	private boolean unsatisIncludedInCombination(String combinacion) {

		boolean bRes=false;

		// Parts of the combination to be valued

		String[] aCmbTratar = combinacion.split("-");	
		List<String> lCmbATratar=new ArrayList<String>();
		Collections.addAll(lCmbATratar, aCmbTratar);

		for (String cmbUnSatisfiable: listUnSatisfiables) {

			// Parts of each unsatisfiable combination
			String[] aCmbUnSat = cmbUnSatisfiable.split("-");	

			boolean todasExisten=true;
			for (int nCmb=0;nCmb<aCmbUnSat.length;nCmb++) {
				String parte = aCmbUnSat[nCmb];
				// If a part of the combination to be treated does not exist, the combination must be treated

				if (!lCmbATratar.contains(parte)) {
					todasExisten=false;
					nCmb=aCmbUnSat.length;
					continue;
				}
			}
			if (todasExisten) {
				storeResultCmb(combinacion, "UNSATISFIABLE", "Indirect calculation. Contains ("+cmbUnSatisfiable+")");
				if (!listUnSatisfiables.contains(combinacion)) {
					listUnSatisfiables.add(combinacion);
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
///**
// * Stores a class and an attribute (deprecated)
// * @author Juanto
// *
// */
//class KeyClassAttrOld {
//	String nomClase;
//	String nomAttr;
//	public KeyClassAttrOld(String vNomClase, String vNomAttr) {
//		this.nomClase = vNomClase;
//		this.nomAttr = vNomAttr;
//	}
//}



