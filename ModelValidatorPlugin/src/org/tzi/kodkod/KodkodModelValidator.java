package org.tzi.kodkod;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
import org.tzi.kodkod.helper.LogMessages;
import org.tzi.kodkod.model.iface.IClass;
import org.tzi.kodkod.model.iface.IInvariant;
import org.tzi.kodkod.model.iface.IModel;
import org.tzi.mvm.InfoInv;
import org.tzi.mvm.KeyAttrInv;
import org.tzi.mvm.KeyClassAttr;
import org.tzi.mvm.MVMStatisticsVisitor;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.kodkod.plugin.gui.ValidatorMVMDialogSimple;
import org.tzi.use.main.Session;
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
 */
public abstract class KodkodModelValidator {

	private static final Logger LOG = Logger.getLogger(KodkodModelValidator.class);

	protected IModel model;
	protected Session session;
	protected Solution solution;
	protected Evaluator evaluator;

	public static HashMap<String, String> listCmb = new HashMap<>();
	public static HashMap<String, String> listCmbSel = new HashMap<>();
	public static HashMap<String, String> mapGRP_SAT_MAX = new HashMap<>();
	public static HashMap<String, ResInv> mapInvRes = new HashMap<>();

	//	public static HashMap<KeyClassAttr, Collection<MClassInvariant>> mapResVis = new HashMap<>();
	public static HashMap<MClass, List<KeyClassAttr>> mapCAI = new HashMap<>();	
	public static HashMap<MClassInvariant, InfoInv> mapInfoInv = new HashMap<>();	
	
	// guardar en Visitor *********************************
	public static HashMap<MAttribute, List<MClassInvariant>> mapInfoAttr = new HashMap<>();	

	public static List<ResComb> listCmbRes = new ArrayList<ResComb>();
	public static List<ResInv> listInvRes = new ArrayList<ResInv>();

	public static List<String> listSatisfiables= new ArrayList<String>();
	public static List<String> listUnSatisfiables= new ArrayList<String>();
	public static List<String> listUnSatisfiablesTotal= new ArrayList<String>();
	public static List<String> listOthers= new ArrayList<String>();

	private boolean debMVM=false;

	public static boolean showResultMix  = true;
	/**
	 * Show the result of NOT repeated combinations
	 */
	public static boolean showSummarizeResults  = false;

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
	public void validateVariable(IModel model, MModel mModel, Session session ) {
		// Save initial time to later calculate the time it takes
		Instant start = Instant.now();
		this.model = model;
		this.session=session;
		evaluator = null;
		listCmb.clear();
		listCmbSel.clear();
		listCmbRes.clear();
		mapInvRes.clear();

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
			Collection<IInvariant> invClassTotal = new ArrayList<IInvariant>();

			for (IClass oClass: model.classes()) {
				invClassTotal.addAll(oClass.invariants());
			}
			// First pass to see which invariants are no longer satisfiable even if they are alone
			for (IInvariant invClass: invClassTotal) {
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

				System.out.println("MVM: Invariants State: " + strCombinacion);
				if (solution.outcome().toString() == "SATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_SATISFIABLE") {
					invClassSatisfiables.add(invClass);
					invRes = new ResInv(strNameInv, "SATISFIABLE", nOrdenInv,invClass);

					//					int totalInv = invClassTotal.size();
					//					String strNOrdenInv = String.format("%0"+String.valueOf(totalInv).length()+"d",nOrdenInv);
					//					listSatisfiables.add(String.valueOf(strNOrdenInv));
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
			// Individual Results
			showResult(invClassSatisfiables,  invClassUnSatisfiables, invClassOthers);

			// We look for variables of each OCL expression
			LOG.info("MVM: Tratamiento OCL");
			//analysis_OCL(model, mModel,invClassSatisfiables);
			analysis_OCL(model, mModel,invClassSatisfiables);			

			if (false) {

				//Hacer combinaciones
				LOG.info("MVM: Inicio fabricacion de combinaciones con invariantes satisfiables.");
				samples = new HashMap<>();
				int i = 0;
				for (IInvariant invClass: invClassSatisfiables) {
					// Buscar la inv satis en listInvRes para obtener el orden
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
				// Ordenar lista antes de enviar a validar 
				List<String> listSorted = new ArrayList<>(listCmbSel.keySet());
				List<String> listSortedByCmb = listSorted;
				// Aqui hemos de ordenar por numero de combinaciones de mayor a menor
				listSortedByCmb = sortByCmbNumber(listSorted, invClassTotal.size());
				LOG.info("MVM: Envio a sendToValidate.");
				sendToValidate(listSortedByCmb , invClassTotal ); 

				// Compactacion de resultados
				// Si 1-2-3 es SAT y 1-2-4 tambien tenemos el grupo (1-2) que puede ser SAT con 3 o con 4
				busca_grupos_SAT_MAX();

				showResultGral();
				Instant end = Instant.now();
				Duration timeElapsed = Duration.between(start, end);
				LOG.info("MVM: Time taken: "+ timeElapsed.toMillis() +" milliseconds");

				//			ValidatorMVMDialog validatorMVMDialog= 
				//					new ValidatorMVMDialog(MainWindow.instance(), 
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
			}// este sobra cuando se 'reviva el codigo'
		} catch (Exception e) {
			e.printStackTrace();
		}

	}
	private void analysis_OCL(IModel iModel,MModel mModel,Collection<IInvariant> invClassSatisfiables) {
		Collection<MClassInvariant> col = mModel.classInvariants();
		mapCAI.clear();
		mapInfoInv.clear();
		int contador = 0;
		int conLog=0;
		List<String> logs = new ArrayList<String>();

		for(MClassInvariant inv: col) {
			
			Expression exp = inv.bodyExpression();
			MVMStatisticsVisitor visitor = new MVMStatisticsVisitor();
			visitor.setLogs(logs);
			visitor.setConLog(conLog);
			visitor.setMapCAI(mapCAI);
			// mapInfoInv
			visitor.setMapInfoInv(mapInfoInv);
			visitor.setClassInv(inv);
			exp.processWithVisitor(visitor);
			logs = visitor.getLogs();
			conLog=visitor.getConLog();
			mapCAI = visitor.getMapCAI();
			mapInfoInv=visitor.getMapInfoInv();
			contador+=1;

			System.out.println("contador [" + contador + "]");
		}
		for(String log: logs) {
			System.out.println("log [" + log + "]");
		}
		//Aqui3
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
			}
		}
	}

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

	}

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
	}

	/**
	 * Get all possible combinations
	 * @param invariantes to mix
	 */
	public static void mixInvariants(Map<Integer, IInvariant> samples) {
		int nInvs = samples.size();

		System.out.println("\nInvariants to treat: (" + nInvs + ")");
		System.out.println("----------------------------");

		int nTrata = 0;
		for (Entry<Integer, IInvariant> obj : samples.entrySet()) 
		{

			nTrata = obj.getKey();
			String nameInv = obj.getValue().name();
			System.out.println("MVM: a tratar " +nTrata+" " + nameInv);
		}

		System.out.println("----------------------------");
		System.out.println();

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

			Integer kInv = getKeyElement(samples, nInv);

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
			System.out.println("Encuentra " + keyOrdenada + " y guarda "+combination);
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

		String head="Send to Validator ("+ listSorted+") combinations. (listSorted)";
		System.out.println(head);
		System.out.println(("-").repeat(head.length()));
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
					System.out.println("MVM: " + resultado);
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
		System.out.println("MVM: Entra en calcular (" + combinacion + ")");
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
		System.out.println("MVM: Entra en calcularRec (" + combinacion + ")");
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
				List<IInvariant> listInv = new ArrayList<IInvariant>();
				listInv=splitInvCombination( newCmb);
				Solution solution = null;
				try {
					solution = calcular( newCmb,  invClassTotal,  kodkodSolver);
				} catch (Exception e) {
					e.printStackTrace();
				}
				acumVal+=1;

				String resultado = cmbSel + " " + acumVal+ " " + String.format("%-20s",newCmb);
				resultado += " - ["+ solution.outcome()+"]";
				System.out.println("MVM - calcularRec: " + resultado);

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


