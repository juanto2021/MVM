package org.tzi.kodkod;

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
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.kodkod.plugin.ResValidation;
import org.tzi.use.kodkod.plugin.gui.ValidatorJuantoDialog;
import org.tzi.use.uml.mm.MModel;

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
	protected Solution solution;
	protected Evaluator evaluator;

	public static HashMap<String, String> listCmb = new HashMap<>();
	public static HashMap<String, String> listCmbSel = new HashMap<>();
	public static List<ResComb> listCmbRes = new ArrayList<ResComb>();

	public static List<String> listSatisfiables= new ArrayList<String>();
	public static List<String> listUnSatisfiables= new ArrayList<String>();
	public static List<String> listOthers= new ArrayList<String>();
	
	// Definir clase interna para resultado con:
	// - Combinacion
	// - Resultado (sat/unsat)
	// Explicacion

//	public class ResComb {
//		String combinacion;
//		String resultado;
//		String comentario;
//		public ResComb(String strCombinacion, String strResultado, String strComentario) {
//
//			this.combinacion = strCombinacion;
//			this.resultado = strResultado;
//			this.comentario = strComentario;
//		}
//		
//	}

	private boolean debJG=false;

	public static boolean showResultMix  = true;
	/**
	 * Show the result of NOT repeated combinations
	 */
	public static boolean showSummarizeResults  = true;
	/**
	 * Shows the combinations to send to the validator
	 */
	public static boolean showCmbSendToValidator  = true;

	/**
	 * Final result of the validation of all useful combinations
	 */
	public static List<ResValidation> listResValidation = new ArrayList<ResValidation>();

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
		LOG.info("MMV: Llama a solve desde validate en KodkodModelValidator");
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
		LOG.info("MMV: Llega solution en validate en KodkodModelValidator " + solution.outcome());

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
	public void validateVariable(IModel model, MModel mModel) {
		// Guardar tiempo inicial para posteriormente calcular el tiempo que se tarda
		this.model = model;
		evaluator = null;
		listCmb.clear();
		listCmbSel.clear();

		listSatisfiables.clear();
		listUnSatisfiables.clear();
		listOthers.clear();

		KodkodSolver kodkodSolver = new KodkodSolver();

		Collection<IInvariant> invClassSatisfiables = new ArrayList<IInvariant>();
		Collection<IInvariant> invClassUnSatisfiables = new ArrayList<IInvariant>();
		Collection<IInvariant> invClassOthers = new ArrayList<IInvariant>();

		try {
			LOG.info("MMV: (2) Llama a solve desde validateVariable en KodkodModelValidator");
			Collection<IInvariant> invClassTotal = new ArrayList<IInvariant>();

			for (IClass oClass: model.classes()) {
				invClassTotal.addAll(oClass.invariants());
			}
			// Primera pasada para ver que invariantes ya no son satisfiables aunque esten solas
			for (IInvariant invClass: invClassTotal) {
				invClass.activate();
				String strCombinacion = invClass.clazz().name()+": [A] " + invClass.name();
				// Deshabilitamos las demas
				for (IInvariant invClass2: invClassTotal) {
					if (invClass2.name()!=invClass.name()) {
						invClass2.deactivate();
						strCombinacion += " - [I] "+ invClass2.name();
					}
				}

				kodkodSolver = new KodkodSolver();
				solution = kodkodSolver.solve(model);

				strCombinacion += " - ["+ solution.outcome()+"]";
				System.out.println("MMV: Invariants State: " + strCombinacion);
				if (solution.outcome().toString() == "SATISFIABLE") {
					invClassSatisfiables.add(invClass);
					
				}else if (solution.outcome().toString() == "UNSATISFIABLE") {
					invClassUnSatisfiables.add(invClass);
				} else {
					invClassOthers.add(invClass);
				}
			}
			// Resultados Individuales
			showResult(invClassSatisfiables,  invClassUnSatisfiables, invClassOthers);

			//Hacer combinaciones

			samples = new HashMap<>();
			int i = 0;
			for (IInvariant invClass: invClassSatisfiables) {
				i+=1;
				samples.put(i, invClass);

			}

			mixInvariants(samples); 
			if (debJG) {
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

			// Ordenar lista antes de enviara validar 
			List<String> listSorted = new ArrayList<>(listCmbSel.keySet());
			List<String> listSortedByCmb = listSorted;
			// Aqui hemos de ordenar por numero de combinaciones de mayor a menor
			listSortedByCmb = sortByCmbNumber(listSorted);

			sendToValidate(listSortedByCmb , invClassTotal ); //JG	
			showResultGral();
			ValidatorJuantoDialog validatorJuantoDialog= 
					new ValidatorJuantoDialog(MainWindow.instance(), 
							invClassSatisfiables, 
							invClassUnSatisfiables, 
							invClassOthers,
							listSatisfiables,
							listUnSatisfiables,
							listOthers,
							mModel);
		} catch (Exception e) {
			e.printStackTrace();
		}
// Calcular el tiempo final
	}

	private List<String> sortByCmbNumber(List<String> listSorted) {
		List<String> listRes = new ArrayList<>();

		HashMap<String, String> listRk = new HashMap<>();
		for (String strCmb: listSorted) {
			int nGrupos = listSorted.size() - (strCmb.length()-strCmb.replace("-","").length())+1;

			// Hallar Key que le corresponde si ordenamos sus partes
			String keyOrdenada = nGrupos + " - " + strCmb;

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
			String valor=strCmb.split(" ")[2];
			listResLimpia.add(valor);
		}

		return listResLimpia;
	}

	private void showResult(Collection<IInvariant> invClassSatisfiables, 
			Collection<IInvariant> invClassUnSatisfiables,
			Collection<IInvariant> invClassOthers) {

		System.out.println();
		System.out.println("MMV: SATISFIABLES");
		for (IInvariant invClass: invClassSatisfiables) {
			System.out.println("MMV: " + invClass.name());
		}

		System.out.println();
		System.out.println("MMV: UNSATISFIABLES");
		for (IInvariant invClass: invClassUnSatisfiables) {
			System.out.println("MMV: " + invClass.name());
		}

		if(invClassOthers.size()>0) {
			System.out.println();
			System.out.println("MMV: OTHERS");
			for (IInvariant invClass: invClassOthers) {
				System.out.println("MMV: " + invClass.name());
			}
		}
	}


	private void showResultGral() {

		System.out.println();
		System.out.println("MMV: SATISFIABLES ["+ listSatisfiables.size()+"]");
		for (String cmbSatisfiable: listSatisfiables) {
			System.out.println("MMV: " + cmbSatisfiable);
		}

		System.out.println();
		System.out.println("MMV: UNSATISFIABLES ["+ listUnSatisfiables.size()+"]");
		for (String cmbUnSatisfiable: listUnSatisfiables) {
			System.out.println("MMV: " + cmbUnSatisfiable);
		}

		if(listOthers.size()>0) {
			System.out.println();
			System.out.println("MMV: OTHERS ["+ listOthers.size()+"]");
			for (String cmbOther: listOthers) {
				System.out.println("MMV: " + cmbOther);
			}
		}
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
			nTrata+=1;
			System.out.println("MMV: a tratar " +nTrata+" " + obj.getValue().name());
		}

		System.out.println("----------------------------");
		System.out.println();

		for (int nInv = 1; nInv < nInvs+1; nInv++) {
			int nivel=1;
			String base=nInv+"";
			storeResult(base);
			if (nivel <nInvs) {
				extendLevel(base, nivel+1,nInvs); 
			}
		}

	}

	/**
	 * Recursive method that finds groups from 1 to n invariants
	 * @param baseIn part of previous combination
	 * @param nivel level to mix
	 * @param nInvs number of invariants
	 */
	public static void extendLevel(String baseIn, int nivel,int nInvs) {
		for (int nInv = 1; nInv < nInvs+1; nInv++) {
			String base=baseIn;
			if (!base.equals("")) {
				base+="-";
			}
			base+=nInv;
			storeResult(base);
			if (nivel < nInvs) {
				extendLevel( base, nivel+1,nInvs); 
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
		}else {
			// Si no esta usada, almacenamos con valor 'N' (Nueva)
			valor="N";  
			listCmb.put(keyOrdenada, valor);
			listCmbSel.put(keyOrdenada, combination);
		}

	}
	
	public static void storeResultCmb(String combination, String resultado, String comentario) {
		ResComb res = new ResComb(combination, resultado, comentario);
		listCmbRes.add(res);
		
//		ResComb
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

		String head="Send to Validator ("+ listCmbSel.size()+") combinations.";
		System.out.println(head);
		System.out.println(("-").repeat(head.length()));

		listResValidation.clear();
		KodkodSolver kodkodSolver = new KodkodSolver();
		List<IInvariant> listInv = new ArrayList<IInvariant>();
		for (String combinacion: listSorted) 
		{
			// Ver si la combinacion se halla incluida en una satisfactible
			// Si la combinacion esta incluida en alguna combinacion satisfactible
			// no hace falta calcularla porque tambien sera satisfactible

			boolean calculate=true;
			calculate = !includedInSatisfactible(combinacion);

			if (calculate) {
				// Ver si hay combinaciones insatisfactibles que esten incluidas en la combinacion a tratar
				calculate = !unsatisIncludedInCombination( combinacion);
			}

			if (calculate) {
				// Buscar invariantes de la combinacion
				listInv=splitInvCombination( combinacion);

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
					solution = kodkodSolver.solve(model);
				} catch (Exception e) {
					e.printStackTrace();
				}
				String resultado = String.format("%-20s",combinacion);
				resultado += " - ["+ solution.outcome()+"]";
				System.out.println("MMV: " + resultado);
				if (showCmbSendToValidator) {
					System.out.println(listaActivas);
				}
				if (solution.outcome().toString() == "SATISFIABLE") {
					listSatisfiables.add(combinacion);
					storeResultCmb(combinacion, "SATISFIABLE", "Calculo directo");
				}else if (solution.outcome().toString() == "UNSATISFIABLE") {
					listUnSatisfiables.add(combinacion);
					storeResultCmb(combinacion, "UNSATISFIABLE", "Calculo directo");
				} else {
					listOthers.add(combinacion);
				}

				// Store result of that validation
				ResValidation resValidation = new ResValidation( listInv, solution.outcome().toString());
				listResValidation.add(resValidation);
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
				storeResultCmb(combinacion, "SATISFIABLE", "Calculo indirecto. Ya existe en combinacion ("+cmbSatisfiable+")");
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
					nCmb=aCmbTratar.length;
					continue;
				}
			}
			if (todasExisten) {
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
