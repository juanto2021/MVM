package org.tzi.kodkod;

import java.awt.BorderLayout;
import java.awt.Cursor;
import java.awt.Dimension;
import java.beans.PropertyVetoException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import javax.swing.JComponent;
import javax.swing.JDesktopPane;
import javax.swing.JDialog;
import javax.swing.JInternalFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.SwingWorker;

import org.apache.log4j.Logger;
import org.tzi.kodkod.helper.LogMessages;
import org.tzi.kodkod.model.iface.IAssociation;
import org.tzi.kodkod.model.iface.IAssociationEnd;
import org.tzi.kodkod.model.iface.IClass;
import org.tzi.kodkod.model.iface.IInvariant; 
import org.tzi.kodkod.model.iface.IModel;
import org.tzi.mvm.CollectionBitSet;
import org.tzi.mvm.Combination;
import org.tzi.mvm.ConfigMVM;
import org.tzi.mvm.InfoAssoc;
import org.tzi.mvm.InfoAttr;
import org.tzi.mvm.InfoInv;
import org.tzi.mvm.KeyAttrInv;
import org.tzi.mvm.KeyClassAttr;
import org.tzi.mvm.MVMStatisticsVisitor;
import org.tzi.mvm.ParamDialogValidator;
import org.tzi.use.api.UseApiException;
import org.tzi.use.api.UseSystemApi;
import org.tzi.use.config.Options;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.gui.main.ViewFrame;
import org.tzi.use.gui.views.ClassInvariantView;
import org.tzi.use.gui.views.diagrams.DiagramView.LayoutType;
import org.tzi.use.gui.views.diagrams.objectdiagram.NewObjectDiagramView;
import org.tzi.use.gui.views.evalbrowser.ExprEvalBrowser;
import org.tzi.use.kodkod.plugin.PluginModelFactory;
import org.tzi.use.kodkod.plugin.gui.ValidatorMVMDialogSimple;
import org.tzi.use.kodkod.solution.ObjectDiagramCreator;
import org.tzi.use.main.Session;
import org.tzi.use.parser.ocl.OCLCompiler;
import org.tzi.use.uml.mm.MAssociation;
import org.tzi.use.uml.mm.MAttribute;
import org.tzi.use.uml.mm.MClass;
import org.tzi.use.uml.mm.MClassInvariant;
import org.tzi.use.uml.mm.MElementAnnotation;
import org.tzi.use.uml.mm.MInvalidModelException;
import org.tzi.use.uml.mm.MModel;
import org.tzi.use.uml.mm.ModelFactory;
import org.tzi.use.uml.ocl.expr.Expression;
import org.tzi.use.uml.ocl.expr.MultiplicityViolationException;
import org.tzi.use.uml.ocl.type.EnumType;
import org.tzi.use.uml.ocl.value.BooleanValue;
import org.tzi.use.uml.ocl.value.Value;
import org.tzi.use.uml.sys.MObject;
import org.tzi.use.uml.sys.MSystemException;
import org.tzi.use.uml.sys.MSystemState;
import org.tzi.use.uml.sys.soil.MAttributeAssignmentStatement;
import org.tzi.use.uml.sys.soil.MNewObjectStatement;
import org.tzi.use.util.StringUtil;
import org.tzi.use.util.TeeWriter;
import org.tzi.use.util.USEWriter;

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

	protected static IModel model;
	protected Session session;
	protected static Solution solution;
	protected Evaluator evaluator;
	protected static KodkodSolver kodkodSolver;

	public int invsMModel;
	public int invsIModel;

	public static Collection<IInvariant> invClassTotal = new ArrayList<IInvariant>();
	public static Collection<IInvariant> invClassTotalBck = new ArrayList<IInvariant>();

	public static Collection<MClassInvariant> invClassTotalMC = new ArrayList<MClassInvariant>();
	public static Collection<MClassInvariant> invClassTotalBckMC = new ArrayList<MClassInvariant>();

	public static HashMap<String, String> listCmb = new HashMap<>();
	public static HashMap<String, String> listCmbSel = new HashMap<>();

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
	public static List<BitSet> listCmbB = new ArrayList<BitSet>();

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
	private static Instant timeInitFind=null;
	private static Instant timeFinFind=null;
	private static Duration timeDeactivateAll=null;
	private static Duration timeCalcIndividually=null;
	private static Duration timeBruteCombCalc=null;
	private static Duration timeCallSolver=Duration.between(Instant.now(), Instant.now());

	/**
	 * Show the result of NOT repeated combinations
	 */
	public static boolean showStructuresAO  = false; // Analysis OCL
	public static boolean showSummarizeResults  = false;
	public static boolean showSatisfiables = false;
	public static boolean showUnsatisfiables = false;
	public static boolean showOthers = false;	

	public static int numCallSolver=0;
	public static int numCallSolverSAT=0;
	public static int numCallSolverUNSAT=0;

	public static int numCmbsTOTAL=0;
	public static int numCmbsSAT=0;
	public static int numCmbsUNSAT=0;

	private List<Future<EvalResult>> futures;

	private static EventThreads threadGreedy;
	private static boolean calON;
	private static boolean stopBrute=false;

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

	public static List<BitSet> lBitCmb= new ArrayList<BitSet>();

	public ParamDialogValidator param;


	/**
	 * Validates the given model.
	 * 
	 * @param model
	 */
	public void validate(IModel model) {
		this.model = model;
		evaluator = null;

		kodkodSolver = new KodkodSolver();
		if (debMVM) {
			LOG.info("MVM: Llama a solver desde validate en KodkodModelValidator");
		}

		try {
			solution = call_Solver(model);
		} catch (Exception e) {
			LOG.error(LogMessages.validationException + " (" + e.getMessage() + ")");
			return;
		} catch (OutOfMemoryError oome) {
			LOG.error(LogMessages.validationOutOfMemory + " (" + oome.getMessage() + ")");
			return;
		}
		LOG.info(solution.outcome());
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
	 * Concentrate calls to Solver
	 * @param model
	 * @return
	 */
	public Solution call_Solver(IModel model) {
		Solution solution = null;
		try {
			Instant iniSolver = Instant.now();


			solution = kodkodSolver.solve(model);
			Instant endSolver = Instant.now();
			Duration timeSolver = Duration.between(iniSolver, endSolver);
			timeCallSolver = timeCallSolver.plus(timeSolver);
		} catch (Exception e) {
			LOG.error(LogMessages.validationException + " (" + e.getMessage() + ")");
		} catch (OutOfMemoryError oome) {
			LOG.error(LogMessages.validationOutOfMemory + " (" + oome.getMessage() + ")");
		}
		return solution;
	}

	public boolean show_inv_state_dialog(MModel model) {
		boolean res=false;
		ClassInvariantView civ = new ClassInvariantView(MainWindow.instance(),
				session.system());
		ViewFrame f = new ViewFrame("Class invariants", civ,
				"InvariantView.gif");

		civ.setViewFrame(f);
		JComponent c = (JComponent) f.getContentPane();
		c.setLayout(new BorderLayout());
		c.add(civ, BorderLayout.CENTER);

		MainWindow.instance().addNewViewFrame(f);
		System.out.println("Showed");
		return res;
	}

	// Method call testing

	public void test_call_methods(MModel model, IModel iModelOri) {
		//------------------------------------------------------------------------------------		
		// Evaluates OCL expressions
		String result="";
		String expression = "2+3";
		result = test_eval_expr(expression);
		System.out.println("Evalua ["+expression+"] = ["+result+"]");
		expression = "2+3+6+10";
		result = test_eval_expr(expression);
		System.out.println("Evalua ["+expression+"] = ["+result+"]");
		System.out.println();
		//------------------------------------------------------------------------------------
		// Create object p1 y p2
		String sClassName="Person";
		MClass objectClass=model.getClass(sClassName);
		String nomObj="p1";
		boolean res = test_create_object( objectClass, nomObj);
		System.out.println("Crea ["+nomObj+"] = ["+res+"]");
		nomObj="p2";
		res = test_create_object( objectClass, nomObj);
		System.out.println("Crea ["+nomObj+"] = ["+res+"]");

		//------------------------------------------------------------------------------------
		// Asign values to attributes

		nomObj="p1";
		String sAttrValue = "150";
		String sAttrName="age";
		test_assign_value_attr( model, iModelOri, sClassName,nomObj, sAttrName, sAttrValue);
		nomObj="p2";
		sAttrValue = "250";
		sAttrName="age";
		test_assign_value_attr( model, iModelOri, sClassName,nomObj, sAttrName, sAttrValue);
		System.out.println("Values assigned. Done");

		// Check structure
		res=test_check_structure();
		System.out.println("Structure checked. Done ["+res+"}");

		// Show invariants state in consola
		test_inv_state_console(model);

		// Displays invariant states in dialog
		test_inv_state_dialog(model);

		// Show EvalBrowser
		test_show_EvalBrowser(model);		

	}

	public String test_eval_expr(String expression) {
		String result="";
		String in = expression;
		StringWriter msgWriter1 = new StringWriter();
		StringWriter msgWriter2 = new StringWriter();
		PrintWriter out = new PrintWriter(new TeeWriter(
				msgWriter1, msgWriter2), true);
		Expression expr = OCLCompiler.compileExpression(
				session.system().model(),
				session.system().state(),
				in, 
				"Error", 
				out, 
				session.system().varBindings());

		if (expr == null) {
			// try to parse error message and set caret to error position
			String msg = msgWriter2.toString();
			int colon1 = msg.indexOf(':');
			if (colon1 != -1) {
				int colon2 = msg.indexOf(':', colon1 + 1);
				int colon3 = msg.indexOf(':', colon2 + 1);

				try {
					int line = Integer.parseInt(msg.substring(colon1 + 1,
							colon2));
					int column = Integer.parseInt(msg.substring(colon2 + 1,
							colon3));
					int caret = 1 + StringUtil.nthIndexOf(in, line - 1,
							Options.LINE_SEPARATOR);
					caret += column;

					// sanity check
					caret = Math.min(caret, in.length());
				} catch (NumberFormatException ex) { }
			}
		}

		org.tzi.use.uml.ocl.expr.Evaluator evaluator = new org.tzi.use.uml.ocl.expr.Evaluator(false);
		Value val = evaluator.eval(expr, session.system().state(), session.system()
				.varBindings());
		result = val.toString();
		return result;
	}

	public boolean test_create_object(MClass objectClass, String objectName) {
		boolean result=false;
		try {
			MNewObjectStatement statement = 
					new MNewObjectStatement(objectClass, objectName);

			USEWriter.getInstance().protocol(
					"[GUI] " + statement.getShellCommand().substring(1));

			session.system().execute(statement);

		} catch (MSystemException e) {
			System.out.println("error ["+e.getMessage()+"]");
		}
		return result;		
	}

	public boolean test_assign_value_attr(MModel model, IModel iModelOri,String sClassName, 
			String sObjName, String sAttrName, String sAttrValue) {
		boolean res=false;
		MClass objectClass=model.getClass(sClassName);
		MAttribute attribute = objectClass.attribute(sAttrName, false);
		StringWriter errorOutput = new StringWriter();
		Expression valueAsExpression = 
				OCLCompiler.compileExpression(
						session.system().model(),
						session.system().state(),
						sAttrValue, 
						"<input>", 
						new PrintWriter(errorOutput, true), 
						session.system().varBindings());

		MSystemState state = session.system().state();
		MObject fObject = state.objectByName(sObjName);

		try {
			session.system().execute(
					new MAttributeAssignmentStatement(
							fObject, 
							attribute, 
							valueAsExpression));
		} catch (MSystemException e) {
			e.printStackTrace();
		}		
		return res;
	}

	public boolean test_check_structure() {
		// Check the structure
		PrintWriter fLogWriter;
		StringWriter msgWriter1 = new StringWriter();
		fLogWriter = new PrintWriter(msgWriter1, true);
		boolean res = session.system().state().checkStructure(fLogWriter);
		System.out.println("Structure checked. Done");
		return res;
	}

	public boolean test_inv_state_console(MModel model) {
		boolean res=false;
		for (MClassInvariant mc:model.classInvariants() ) {
			System.out.println("mc ["+mc+"]");
		}

		MClassInvariant[] fClassInvariants = new MClassInvariant[0];
		int n = model.classInvariants().size();
		fClassInvariants = new MClassInvariant[n];
		System.arraycopy(model.classInvariants().toArray(), 0,
				fClassInvariants, 0, n);
		Arrays.sort(fClassInvariants);


		for (int i = 0; i < fClassInvariants.length; i++) {
			if(!fClassInvariants[i].isActive()){
				continue;
			}

			MClassInvariant inv;
			inv = fClassInvariants[i];
			Expression exp = inv.bodyExpression();
			System.out.println("inv ["+inv.name()+"] exp ["+exp+"]");
			MSystemState systemState;
			systemState = session.system().state();

			org.tzi.use.uml.ocl.expr.Evaluator eval = new org.tzi.use.uml.ocl.expr.Evaluator();
			Value v = null;
			String message = null;
			long start = System.currentTimeMillis();

			try {
				v = eval.eval(inv.flaggedExpression(), systemState);
			} catch (MultiplicityViolationException e) {
				message = e.getMessage();
			}

		}
		return res;
	}
	private boolean checkStructure() {

		StringWriter buffer = new StringWriter();
		PrintWriter out = new PrintWriter(buffer);

		boolean ok = session.system().state().checkStructure(out);
		//		boolean res=false;
		// check all associations
		boolean reportAllErrors = true;
		for (MAssociation assoc : session.system().model().associations()) {
			StringWriter buffer2 = new StringWriter();
			PrintWriter out2 = new PrintWriter(buffer2);
			//			boolean res = session.system().state().checkStructure(assoc, out2, reportAllErrors) ;
			// AQUI
			session.system().state().checkStructure(assoc, out2, reportAllErrors) ;
		}

		return ok;
	}
	private EvalResult[] load_Values() {
		MModel fModel = session.system().model();
		int n = fModel.classInvariants().size();
		MClassInvariant[] fClassInvariants = new MClassInvariant[0];
		fClassInvariants = new MClassInvariant[n];
		System.arraycopy(fModel.classInvariants().toArray(), 0,
				fClassInvariants, 0, n);
		Arrays.sort(fClassInvariants);
		EvalResult[] fValues;
		fValues = new EvalResult[n];
		for (int i = 0; i < fValues.length; i++) {
			fValues[i] = null;
		}
		ExecutorService executor = Executors.newFixedThreadPool(Options.EVAL_NUMTHREADS);
		futures = new ArrayList<Future<EvalResult>>();
		ExecutorCompletionService<EvalResult> ecs = new ExecutorCompletionService<EvalResult>(executor);
		boolean violationLabel = false; 
		int numFailures = 0;
		boolean structureOK = true;
		for (int i = 0; i < fClassInvariants.length; i++) {
			if(!fClassInvariants[i].isActive()){
				continue;
			}
			MyEvaluatorCallable cb = new MyEvaluatorCallable(session.system().state(), i, fClassInvariants[i]);
			futures.add(ecs.submit(cb));
		}

		for (int i = 0; i < fClassInvariants.length && !isCancelled(); i++) {
			if(!fClassInvariants[i].isActive()){
				continue;
			}
			try {
				EvalResult res;
				res = ecs.take().get();
				fValues[res.index] = res;

				boolean ok = false;
				// if v == null it is not considered as a failure, rather it is
				// a MultiplicityViolation and it is skipped as failure count
				boolean skip = false;
				if (res.result != null) {
					ok = res.result.isDefined() && ((BooleanValue)res.result).isTrue();
				} else {
					violationLabel = true;
					skip = true;
				}

				if (!skip && !ok)
					numFailures++;

			} catch (InterruptedException ex) {
				break;
			} catch (ExecutionException e) {
				e.printStackTrace();
			}
		}

		for (Future<EvalResult> f : futures) {
			f.cancel(true);
		}
		executor.shutdown();
		return fValues;
	}

	/*
	 * Checks the state of invariants
	 */
	public boolean check_inv_state() {
		//		boolean bRes = false;

		EvalResult[] fValues = load_Values();
		MModel fModel = session.system().model();
		int n = fModel.classInvariants().size();
		MClassInvariant[] fClassInvariants = new MClassInvariant[0];
		fClassInvariants = new MClassInvariant[n];
		System.arraycopy(fModel.classInvariants().toArray(), 0,
				fClassInvariants, 0, n);
		Arrays.sort(fClassInvariants);
		boolean todosOk=true;
		for (EvalResult res : fValues) {
			Boolean boolRes=  ((BooleanValue)res.result).value();

			if (boolRes.equals(false)) todosOk=false;
		}

		return todosOk;

	}
	private boolean check_inv_state_one(MClassInvariant invMClass) {
		boolean bRes=false;
		EvalResult[] fValues = load_Values();
		MModel fModel = session.system().model();
		int n = fModel.classInvariants().size();
		MClassInvariant[] fClassInvariants = new MClassInvariant[0];
		fClassInvariants = new MClassInvariant[n];
		System.arraycopy(fModel.classInvariants().toArray(), 0,
				fClassInvariants, 0, n);
		Arrays.sort(fClassInvariants);
		for (EvalResult res : fValues) {
			Boolean boolRes=  ((BooleanValue)res.result).value();
			MClassInvariant inv= fClassInvariants[res.index];
			if (invMClass.qualifiedName().equals(inv.qualifiedName())) {
				return boolRes;
			}
		}

		return bRes;
	}
	private class EvalResult {
		public final int index;
		public final Value result;
		public final String message;
		public final long duration;

		public EvalResult(int index, Value result, String message, long duration) {
			this.index = index;
			this.result = result;
			this.message = message;
			this.duration = duration;
		}
	}
	private class MyEvaluatorCallable implements Callable<EvalResult> {
		final int index;
		final MSystemState state;
		final MClassInvariant inv;

		public MyEvaluatorCallable(MSystemState state, int index, MClassInvariant inv) {
			this.state = state;
			this.index = index;
			this.inv = inv;
		}

		@Override
		public EvalResult call() throws Exception {
			if (isCancelled()) return null;

			org.tzi.use.uml.ocl.expr.Evaluator eval = new org.tzi.use.uml.ocl.expr.Evaluator();
			Value v = null;
			String message = null;
			long start = System.currentTimeMillis();

			try {
				v = eval.eval(inv.flaggedExpression(), state);
			} catch (MultiplicityViolationException e) {
				message = e.getMessage();
			}

			return new EvalResult(index, v, message, System.currentTimeMillis() - start);
		}
	}
	public final boolean isCancelled() {
		//        return future.isCancelled();
		return false;
	}
	public boolean test_inv_state_dialog(MModel model) {
		boolean res=false;
		res=show_inv_state_dialog( model);
		return res;
	}

	public boolean test_show_EvalBrowser(MModel model) {
		boolean res=false;
		MClassInvariant[] fClassInvariants = new MClassInvariant[0];
		int n = model.classInvariants().size();
		fClassInvariants = new MClassInvariant[n];
		System.arraycopy(model.classInvariants().toArray(), 0,
				fClassInvariants, 0, n);		
		// For first inv
		Expression expr = fClassInvariants[0].flaggedExpression();		
		org.tzi.use.uml.ocl.expr.Evaluator evaluator = new org.tzi.use.uml.ocl.expr.Evaluator(true);
		try {
			evaluator.eval(expr, session.system().state());
		} catch (MultiplicityViolationException ex) {
			return res;
		}
		ExprEvalBrowser.createPlus(evaluator
				.getEvalNodeRoot(), session.system(), fClassInvariants[0]);	
		// For second inv
		expr = fClassInvariants[1].flaggedExpression();		
		try {
			evaluator.eval(expr, session.system().state());
		} catch (MultiplicityViolationException ex) {
			return res;
		}
		ExprEvalBrowser.createPlus(evaluator
				.getEvalNodeRoot(), session.system(), fClassInvariants[1]);		

		// For third invariant
		expr = fClassInvariants[2].flaggedExpression();		
		try {
			evaluator.eval(expr, session.system().state());
		} catch (MultiplicityViolationException ex) {
			return res;
		}
		ExprEvalBrowser.createPlus(evaluator
				.getEvalNodeRoot(), session.system(), fClassInvariants[2]);				
		return res;
	}

	public void test_creation(MModel model, IModel iModelOri) {

		storeEvaluator(kodkodSolver);
		if(KodkodQueryCache.INSTANCE.isQueryEnabled()){ 
			KodkodQueryCache.INSTANCE.setEvaluator(evaluator); 
		}		

		// Create object of a class
		ModelFactory mFactory = new ModelFactory();
		//		IModelFactory iMFactory = new SimpleFactory();
		MModel mModel = mFactory.createModel("Test");
		System.out.println("Crea modelo MModel");
		try {
			// includes model classes
			for (MClass mClass: model.classes()) {
				mModel.addClass(mClass);
				// Includes invariants
				for (MClassInvariant mClassInv: model.classInvariants(mClass)) {
					mModel.addClassInvariant(mClassInv);
				}
				// Includes associations
				for (MAssociation mClassAssoc: model.associations()) {
					mModel.addAssociation(mClassAssoc);
				}

				Map<String, MElementAnnotation> oAnnot = model.getAllAnnotations();
				//				int nAnnotations = oAnnot.size();

				// Annotations
				for (Entry<String, MElementAnnotation> item : oAnnot.entrySet()){
					//					String key = item.getKey();
					MElementAnnotation oME = item.getValue();
					mModel.addAnnotation(oME);
				}

				for (EnumType mEnumType: model.enumTypes()) {
					mModel.addEnumType(mEnumType);
				}
			}

			// Create IModel

			IModel iModel =  PluginModelFactory.INSTANCE.getModel(mModel);

			Solution solution;
			try {
				solution = kodkodSolver.solve(iModel);
				solution = call_Solver(iModelOri);

				createObjectDiagramCreator( iModelOri,  session, solution);
			} catch (Exception e2) {
				e2.printStackTrace();
			}

			UseSystemApi systemApi = UseSystemApi.create(session);
			// Create object for first class
			int contObj=0;
			int numObjs=2;
			String prefixObj = "obj";

			try {
				for (MClass mClass: model.classes()) {
					for (int n=0;n<numObjs;n++) {
						contObj+=1;
						String nomObj=prefixObj+contObj;
						MObject mObject = systemApi.createObject(mClass.name(), nomObj);
						System.out.println("Crea objeto clase ["+mObject.name()+"]");
					}
				}

			} catch (UseApiException e) {
				e.printStackTrace();
			}

		} catch (MInvalidModelException e1) {
			e1.printStackTrace();
		}

	}

	private void createObjectDiagramCreator(IModel iModel, Session session,Solution solution ) {
		ObjectDiagramCreator odc = new ObjectDiagramCreator(iModel, session);// IModel, session	
		try {
			odc.create(solution.instance().relationTuples());
		} catch (UseApiException e) {
			if (!e.getMessage().contains("Link creation failed!")) {
				e.printStackTrace();
			}
		}

		createObjectDiagramCreatorFrame(iModel, session ); 

	}
	private void createObjectDiagramCreatorFrame(IModel iModel, Session session ) {

		NewObjectDiagramView odv = new NewObjectDiagramView(MainWindow.instance(), session.system());
		ViewFrame f = new ViewFrame("Object diagram ("+iModel.name()+")", odv, "ObjectDiagram.gif");
		int OBJECTS_LARGE_SYSTEM = 100;

		if (session.system().state().allObjects().size() > OBJECTS_LARGE_SYSTEM) {

			int option = JOptionPane.showConfirmDialog(new JPanel(),
					"The current system state contains more then " + OBJECTS_LARGE_SYSTEM + " instances." +
							"This can slow down the object diagram.\r\nDo you want to start with an empty object diagram?",
							"Large system state", JOptionPane.YES_NO_OPTION);

			if (option == JOptionPane.YES_OPTION) {
				odv.getDiagram().hideAll();
			}
		}
		JComponent c = (JComponent) f.getContentPane();
		c.setLayout(new BorderLayout());
		c.add(odv, BorderLayout.CENTER);
		int hSpace=130;
		int vSpace=130;
		odv.getDiagram().startLayoutFormatThread(LayoutType.HierarchicalUpsideDown, hSpace, vSpace, true);

		MainWindow.instance().addNewViewFrame(f);
		MainWindow.instance().getObjectDiagrams().add(odv);

		tile();
		odv.getDiagram().startLayoutFormatThread(LayoutType.HierarchicalUpsideDown, hSpace, vSpace, true);

	}

	/**
	 * Accommodate views
	 */
	private void tile() {
		JDesktopPane fDesk = MainWindow.instance().getFdesk();
		JInternalFrame[] allframes = fDesk.getAllFrames();
		int count = allframes.length;
		if (count == 0)
			return;

		// Determine the necessary grid size
		int sqrt = (int) Math.sqrt(count);
		int rows = sqrt;
		int cols = sqrt;
		if (rows * cols < count) {
			cols++;
			if (rows * cols < count) {
				rows++;
			}
		}

		// Define some initial values for size & location
		Dimension size = fDesk.getSize();

		int w = size.width / cols;
		int h = size.height / rows;
		int x = 0;
		int y = 0;

		// Iterate over the frames, deiconifying any iconified frames and
		// then relocating & resizing each
		for (int i = 0; i < rows; i++) {
			for (int j = 0; j < cols && ((i * cols) + j < count); j++) {
				JInternalFrame f = allframes[(i * cols) + j];

				if (f.isIcon() && !f.isClosed()) {
					try {
						f.setIcon(false);
					} catch (PropertyVetoException ex) {
						// ignored
					}
				}
				fDesk.getDesktopManager().resizeFrame(f, x, y, w, h);
				x += w;
			}
			y += h; // start the next row
			x = 0;
		}

	}

	/**
	 * Validates the given model.
	 * 
	 * @param model (Juanto-v1242)
	 */
	public void validateVariable(IModel model, MModel mModel, Session session, String tipoSearchMSS ) {
		MainWindow.instance().statusBar().showMessage("Searching for combinations using Brute force...");
		this.session=session;
		invsMModel = mModel.classInvariants().size();
		invsIModel = model.classInvariants().size();
		// Save initial time to later calculate the time it takes
		Instant start = Instant.now();
		timeInitFind= Instant.now();
		timeCallSolver=Duration.between(start, start);//
		logTime="";
		numCmbsSAT=0;
		numCmbsUNSAT=0;
		numCmbsTOTAL=0;
		//		debMVM=true;//provis
		this.model = model;
		evaluator = null;
		kodkodSolver = new KodkodSolver();

		listCmb.clear();
		listCmbSel.clear();
		colInvFault.clear();

		invClassTotal.clear();
		listSatisfiables.clear();
		listUnSatisfiables.clear();

		lBitCmbSAT.clear();
		lBitCmbUNSAT.clear();

		numCallSolver=0;
		numCallSolverSAT=0;
		numCallSolverUNSAT=0;

		Collection<IInvariant> invClassSatisfiables = new ArrayList<IInvariant>();
		Collection<IInvariant> invClassUnSatisfiables = new ArrayList<IInvariant>();
		Collection<IInvariant> invClassOthers = new ArrayList<IInvariant>();

		Collection<MClassInvariant> invClassSatisfiablesMC = new ArrayList<MClassInvariant>();
		Collection<MClassInvariant> invClassUnSatisfiablesMC = new ArrayList<MClassInvariant>();
		Collection<MClassInvariant> invClassOthersMC = new ArrayList<MClassInvariant>();

		int nOrdenInv=0;
		try {
			Instant start0 = Instant.now();	
			if (debMVM) {
				LOG.info("MVM: (2) Llama a solver desde validateVariable en KodkodModelValidator. Model ("+model.name()+")");
			}
			LOG.info("MVM: Analysis of invariants individually.");

			int nin=0;// provis

			for (IInvariant oInv: model.classInvariants()){
				if (!invClassTotal.contains(oInv))	{
					invClassTotal.add(oInv);
				}
			}

			//--- AQUI
			for (MClassInvariant oInvMC: mModel.classInvariants()){
				if (!invClassTotalMC.contains(oInvMC))	{
					invClassTotalMC.add(oInvMC);
				}
			}

			longInvs = String.valueOf(invClassTotal.size()).length();

			tabInv = new IInvariant[invClassTotal.size()];
			tabInvMClass = new MClassInvariant[invClassTotal.size()];	

			// At this point, all invariants should be disabled.
			// See if it is possible to create copies of disabled invariants and put them in
			// each iteration of the next loop

			// First pass to disable all invariants
			for (IInvariant invClass: invClassTotal) {
				invClass.deactivate();
			}
			// --- Podria ser si se cambia ... (CHG)
			//			for (MClassInvariant invClassMC: invClassTotalMC) {
			//				invClassMC.setActive(false);
			//			}

			//-----------------------

			Instant end0 = Instant.now();
			timeDeactivateAll = Duration.between(start0, end0);

			AddLogTime("Deactivate all",timeDeactivateAll);

			Instant start1 = Instant.now();
			// First pass to see which invariants are no longer satisfiable even if they are alone
			for (IInvariant invClass: invClassTotal) {

				tabInv[nOrdenInv] = invClass;
				MClassInvariant invMClassOActual=null;
				for (MClassInvariant invMClass: mModel.classInvariants()) {
					if (invMClass.qualifiedName().equals(invClass.qualifiedName())) {
						tabInvMClass[nOrdenInv] = invMClass;
						invMClassOActual=invMClass;
					}					
				}	

				invClass.activate(); // Activate just one
				// Podria ser si se cambia (CHG)
				//				invMClassOActual.setActive(true);

				solution = call_Solver(model);
				numCallSolver+=1;


				boolean bResInvs = check_inv_state();

				// The following instruction would not be necessary if CHG is changed
				invMClassOActual=getMClassInvariantFromIInvariant(mModel,invClass) ;
				boolean bResInvOne = false;
				if (invMClassOActual!=null) {
					bResInvOne=check_inv_state_one(invMClassOActual);
				}
				bResInvOne=false;

				String strNameInv = invClass.clazz().name()+"::"+invClass.name();

				String strNameInvMC = invMClassOActual.cls().name()+"::"+invMClassOActual.name();

				String strCombinacion = "Solution: ["+ solution.outcome()+"] Clazz name: ["+ invClass.clazz().name()+ "]";
				String strCombinacionMC = "Solution: ["+ solution.outcome()+"] Class name: ["+ invMClassOActual.cls().name()+ "]";

				nOrdenInv+=1;
				dispMVM("MVM: ["+nOrdenInv+"] Invariants State: " + strCombinacion);
				dispMVM("MVM: Invariants State: " + strCombinacion);

				if (solution.outcome().toString() == "SATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_SATISFIABLE" ||bResInvOne) {
					invClassSatisfiables.add(invClass);
					invClassSatisfiablesMC.add(invMClassOActual);
					numCallSolverSAT+=1;
				}else if (solution.outcome().toString() == "UNSATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_UNSATISFIABLE") {
					invClassUnSatisfiables.add(invClass);
					invClassUnSatisfiablesMC.add(invMClassOActual);
					BitSet bit=new BitSet();
					bit.set(nOrdenInv-1);
					lBitCmbUNSAT.add(bit);
					numCallSolverUNSAT+=1;
				}

				// At the end we deactivate the treated invariant to leave all of them deactivated.
				invClass.deactivate();
				// Could be if you change to MClassInvariant (CHG)
				//				invMClassOActual.setActive(false);
			}

			if (debMVM) {
				LOG.info("Table of invariantes");
				for (int nInv = 0; nInv < tabInv.length; nInv++) {
					dispMVM("[" + (nInv+1)+ "] ["+ tabInv[nInv].name()+"]");
					System.out.println("[" + (nInv+1)+ "] ["+ tabInv[nInv].name()+"]");
				}
			}
			for (int nInv = 0; nInv < tabInv.length; nInv++) {
				System.out.println("[" + (nInv+1)+ "] ["+ tabInv[nInv].name()+"]");
			}
			Instant end1 = Instant.now();
			timeCalcIndividually = Duration.between(start1, end1);

			AddLogTime("Calc individually",timeCalcIndividually);

			// Methods. Possible calculation methods 
			// New Method 
			// We look for variables of each OCL expression
			// ************************************************************************
			if (debMVM) {
				LOG.info("MVM: Tratamiento OCL");
			}

			boolean bResInvs = check_inv_state();
			bResInvs=false;//provis JG
			boolean bResAssocs = checkStructure();

			if (invClassSatisfiables.size()==0) {
				LOG.info("All invariants are unsatisfiable");
				JOptionPane.showMessageDialog(null,
						"All invariants are unsatisfiable",
						"Information",
						JOptionPane.ERROR_MESSAGE);
				// Restablecer estado iconos de Calculo
				MainWindow.instance().enableAction("ValidationMVMG", true);
				MainWindow.instance().enableAction("ValidationMVMB", true);
				MainWindow.instance().enableAction("StopCalcCmb", false);
			}else {
				if (tipoSearchMSS == "G") {
					analysis_OCL(model, mModel,invClassSatisfiables, invClassUnSatisfiables,invClassOthers,
							invClassSatisfiablesMC, invClassUnSatisfiablesMC,invClassOthersMC, start);	
				}
				//AQUI
				if (tipoSearchMSS == "L") {
					calON=true;
					MainWindow.instance().enableAction("ValidationMVMG", false);
					MainWindow.instance().enableAction("ValidationMVMB", false);
					MainWindow.instance().enableAction("StopCalcCmb", true);

					SwingWorker<Void, Void> worker = new SwingWorker<Void, Void>() {
						@Override
						protected Void doInBackground() {
							bruteForceMethod(model, mModel,
									invClassSatisfiables,
									invClassUnSatisfiables,
									invClassOthers,
									invClassSatisfiablesMC,
									invClassUnSatisfiablesMC,
									invClassOthersMC,
									Instant.now());
							return null;
						}

						@Override
						protected void done() {
							// Aquí sabes que el hilo ha terminado
							System.out.println("The calculation is complete.");
							MainWindow.instance().setCursor(Cursor.getDefaultCursor());
							MainWindow.instance().statusBar().showMessage("");
							MainWindow.instance().enableAction("ValidationMVMG", true);
							MainWindow.instance().enableAction("ValidationMVMB", true);
							MainWindow.instance().enableAction("StopCalcCmb", false);
							calON=false;
						}
					};
					worker.execute();

				}
				model_metrics();
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
	private void bruteForceMethod(IModel iModel,MModel mModel,
			Collection<IInvariant> invClassSatisfiables,
			Collection<IInvariant> invClassUnSatisfiables,
			Collection<IInvariant> invClassOthers,
			Collection<MClassInvariant> invClassSatisfiablesMC,
			Collection<MClassInvariant> invClassUnSatisfiablesMC,
			Collection<MClassInvariant> invClassOthersMC,
			Instant start) {
		// Make combinations
		Instant start6 = Instant.now();	
		if (debMVM) {
			LOG.info("MVM: Inicio fabricacion y calculo de combinaciones con invariantes satisfiables.");
		}
		listSatisfiables.clear();
		listUnSatisfiables.clear();

		lBitCmbSAT.clear();
		lBitCmbUNSAT.clear();

		logTime="";

		BitSet bCmbBase = new BitSet();
		// For SAT
		int i = 0;
		for (IInvariant invClass: invClassSatisfiables) {
			// Search satisfiable inv in listInvRes to obtain then position
			i = searchNumInv(invClass);
			bCmbBase.set(i-1);
			BitSet bit=new BitSet();
			bit.set(i-1);
			lBitCmbSAT = review_store_SAT(lBitCmbSAT,bit);
		}

		//-- possible if MClass is changed (CHG)
		//		int i = 0;
		//		for (MClassInvariant invClassMC: invClassSatisfiablesMC) {
		//			// Search satisfiable inv in listInvRes to obtain then position
		//			i = searchNumInvMC(invClassMC);
		//			bCmbBase.set(i-1);
		//			BitSet bit=new BitSet();
		//			bit.set(i-1);
		//			lBitCmbSAT = review_store_SAT(lBitCmbSAT,bit);
		//		}
		//---



		lBitCmb = comRestoB(bCmbBase,true, null);

		if (stopBrute) {
			stopBrute=false;
			MainWindow.instance().enableAction("ShowDiaCmb", false);
			return;
		}



		// For UNSAT
		i = 0;
		for (IInvariant invClass: invClassUnSatisfiables) {
			// Search satisfiable inv in listInvRes to obtain then position
			i = searchNumInv(invClass);
			bCmbBase.set(i-1);
			BitSet bit=new BitSet();
			bit.set(i-1);
			lBitCmbUNSAT = review_store_UNSAT(lBitCmbUNSAT,bit);
		}

		//-- posible si se cambia MClass (CHG)
		//		i = 0;
		//		for (MClassInvariant invClassMC: invClassUnSatisfiablesMC) {
		//			// Search satisfiable inv in listInvRes to obtain then position
		//			i = searchNumInvMC(invClassMC);
		//			bCmbBase.set(i-1);
		//			BitSet bit=new BitSet();
		//			bit.set(i-1);
		//			lBitCmbUNSAT = review_store_UNSAT(lBitCmbUNSAT,bit);
		//		}		


		// --------------------------------------------------------------------
		// I add lists from the new structures
		TraspasaCHB();
		Instant end6 = Instant.now();
		timeBruteCombCalc = Duration.between(start6, end6);
		AddLogTime("sendToValidate bruteforce",timeBruteCombCalc);

		timeFinFind = Instant.now();
		Duration timeElapsed = Duration.between(timeInitFind, timeFinFind);
		AddLogTime("bruteforce TOTAL",timeElapsed);

		timeFinFind = Instant.now();

		String tipoSearchMSS="L";
		int numberIter=1;

		param = new ParamDialogValidator(
				MainWindow.instance(), 
				this,
				invClassSatisfiables, 
				invClassUnSatisfiables, 
				invClassOthers,
				invClassSatisfiablesMC, 
				invClassUnSatisfiablesMC, 
				invClassOthersMC,					
				listSatisfiables,
				listUnSatisfiables,
				tabInv,
				tabInvMClass,
				mModel,
				invClassTotal,
				timeElapsed,
				numCallSolver,
				numCallSolverSAT,
				numCallSolverUNSAT,
				tipoSearchMSS,
				numberIter,
				numCmbsTOTAL,
				numCmbsSAT,
				numCmbsUNSAT
				);
		showValidatorMVMDialogSimple();


	}
	private void showValidatorMVMDialogSimple() {
		JDialog dia = MainWindow.instance().getValidatorDialog();
		if (dia!=null) {
			dia.setVisible(true);
		}else {
			ValidatorMVMDialogSimple validatorMVMDialog= 
					new ValidatorMVMDialogSimple(param, true);	
			validatorMVMDialog.setVisible(true);//JG
		}
		MainWindow.instance().enableAction("ShowDiaCmb", true);
	}

	private void model_metrics() {
		System.out.println("====================================");
		System.out.println("Model metrics [" + model.name()+"]");
		System.out.println("====================================");
		// Number of Classes
		int nClasses=model.classes().size();
		System.out.println("Number of Classes .......: " + nClasses);
		// Number of Associations
		int nAssociations=model.associations().size();
		System.out.println("Number of Associations ..: " + nAssociations);
		// Number of Invariants (OCL Constraints)
		System.out.println("Invs MModel: " + invsMModel);
		System.out.println("Invs IModel: " + invsIModel);
		System.out.println();
		// Number of Attributes per Class
		System.out.printf("| %-30s | %-10s%n", "Class name", "Attributes");
		System.out.printf("| %-30s | %-10s%n", "------------------------------", "----------");
		for (IClass clazz : model.classes()) {
			System.out.printf("| %-30s | %-10d%n", clazz.name(), clazz.allAttributes().size());
		}
		System.out.println();
		// Number of Association Roles

		System.out.printf("| %-25s | %-10s | %-40s |%n", "Association name", "Num roles", "Roles");
		System.out.println("|---------------------------|------------|------------------------------------------|");

		for (IAssociation assoc : model.associations()) {
			StringBuilder strRoles = new StringBuilder();
			strRoles.append("(");
			for (IAssociationEnd assocEnd : assoc.associationEnds()) {
				if (!strRoles.toString().equals("(")) strRoles.append(", ");
				strRoles.append(assocEnd.name());
			}
			strRoles.append(")");

			System.out.printf("| %-25s | %-10d | %-40s |%n", 
					assoc.name(), 
					assoc.associationEnds().size(), 
					strRoles.toString());
		}
		System.out.println();
	}
	private MClassInvariant getMClassInvariantFromIInvariant(MModel mModel,IInvariant invClass) {
		MClassInvariant invMClass=null;
		for (MClassInvariant invMC: mModel.classInvariants()) {
			if (invMC.qualifiedName().equals(invClass.qualifiedName())) {
				return invMC;
			}					
		}	
		return invMClass;
	}

	private static List<String> combListBitSetStr(List<BitSet> lBitSetV){
		List<String> lString= new ArrayList<String>();
		for (BitSet cmbBit:lBitSetV) {
			String cmb = combBitSetStr(cmbBit);
			lString.add(cmb);
		}
		return lString;
	}

	private static String combBitSetStr(BitSet bit){
		String res ="";
		int nElem = bit.length();
		for (int i=0;i<nElem;i++) {
			if (bit.get(i)) {
				if (res!="") {
					res+="-";
				}
				res+=i+1;			
			}
		}
		return res;
	}

	private List<BitSet> comRestoB(BitSet bRestoIn,boolean prune, EventThreads hilo) {
		List<BitSet> listRes = new ArrayList<BitSet>();
		int nInvsRestoB = bRestoIn.cardinality();
		int nElem = bRestoIn.length();
		boolean calcular=true;
		for (int num=1;num<nInvsRestoB+1;num++) {
			for (int i=0;i<nElem;i++) {
				calcular=true;
				// Take the first element and combine it with all the others.
				if (bRestoIn.get(i)) {
					int pElem = i;
					int cuantos = num;
					int acum=0;
					int sig=pElem+cuantos;
					BitSet invCmb = new BitSet();
					for (int g=pElem;g<nElem*2;g++) {
						if (acum<cuantos) {
							int v=g;
							if (v>nElem) {
								v=g-nElem-1;
							}
							if (bRestoIn.get(v)) {
								invCmb.set(v);
								if (prune) {
									if (!lBitCmbSAT.contains(invCmb) && !lBitCmbUNSAT.contains(invCmb)) {


										String solucion = calcularGreedyCHB(invCmb, true,invClassTotal);
										// si es UNSAT, no hace falta mirar el resto										
										addSolutionGHB(invCmb, solucion);
										if (!solucion.equals("SATISFIABLE")) {	
											calcular=false;
											break;
										}
									}
								}else {
									String solucion = calcularGreedyCHB(invCmb, true,invClassTotal);	
									addSolutionGHB(invCmb, solucion);
									if (!listRes.contains(invCmb)) {
										listRes.add(invCmb);
									}
								}

								acum++;
							}
						}else break;
					}
					// add 1 inv
					if (calcular) {
						for (int j=sig;j<nElem*2;j++) {
							int v = j;
							if (v>nElem) {
								v=v-nElem-1;
							}
							if (bRestoIn.get(v)) {
								BitSet invCmbR = (BitSet) invCmb.clone();
								invCmbR.set(v);
								if (prune) {
									if (!lBitCmbSAT.contains(invCmbR) && !lBitCmbUNSAT.contains(invCmbR)) {
										String solucion = calcularGreedyCHB(invCmbR, true,invClassTotal);	
										addSolutionGHB(invCmbR, solucion);
									}	
								}else {
									String solucion = calcularGreedyCHB(invCmbR, true,invClassTotal);	
									addSolutionGHB(invCmbR, solucion);
									if (!listRes.contains(invCmbR)) {
										listRes.add(invCmbR);
									}
								}
							}
						}
					}

					if (threadGreedy!=null) {
						if (threadGreedy.isInterrupted()) {
							System.out.println("Cancelación solicitada. Terminando cálculo...");
							return listRes;
						}
					}
					if (calON &&stopBrute) {
						System.out.println("Cancelación solicitada. Terminando cálculo...");
						return listRes;
					}
				}
			}
		}
		return listRes;
	}
	private static List<BitSet> review_store_SAT(List<BitSet> listIn, BitSet cmbIn) {
		List<BitSet> listRes1 = new ArrayList<BitSet>();
		List<BitSet> listRes2 = new ArrayList<BitSet>();
		// Compare cmb with each of the existing ones in the list.
		// If cmb includes the one it looks at, it removes the one it looks at
		// If cmb is not included in any, cmb is included at the end

		// First pass to eliminate the cmbs that are contained in the new one that arrives
		int nElem = listIn.size();
		for (int i=0;i<nElem;i++) {
			BitSet cmb=listIn.get(i);
			if (!bitIncludedIn(cmb, cmbIn)) {
				listRes1.add(cmb);
			}
		}
		nElem = listRes1.size();
		// Second pass to see if the next one is contained in any of the remaining ones
		boolean existe=false;
		for (int i=0;i<nElem;i++) {
			BitSet cmb=listRes1.get(i);
			// Is cmb included in cmbIn?
			if (bitIncludedIn( cmbIn,cmb)) {
				existe=true;
			}
			listRes2.add(cmb);
		}
		if (!existe) {
			listRes2.add(cmbIn);
		}
		return listRes2;
	}

	private static List<BitSet> review_store_UNSAT(List<BitSet> listIn, BitSet cmbIn) {
		List<BitSet> listRes1 = new ArrayList<BitSet>();
		List<BitSet> listRes2 = new ArrayList<BitSet>();
		// Compara cmb con cada una de las existentes en lista.
		// If cmb is included in the one being viewed, it is removed by the one being viewed
		// If cmb is not included in any, cmb is included at the end

		// First pass to remove the cmbs that include the new one that arrives
		int nElem = listIn.size();
		for (int i=0;i<nElem;i++) {
			BitSet cmb=listIn.get(i);
			// Is cmbIN included in cmb?

			if (!bitIncludedIn(cmbIn, cmb)) {
				listRes1.add(cmb);
			}
		}		
		nElem = listRes1.size();
		// Second pass to see if the next one contains any of the remaining ones
		boolean existe=false;
		for (int i=0;i<nElem;i++) {
			BitSet cmb=listRes1.get(i);
			// Is cmb included in cmbIn?
			if (bitIncludedIn( cmb, cmbIn)) {
				existe=true;
			}
			listRes2.add(cmb);
		}
		if (!existe) {
			listRes2.add(cmbIn);
		}
		return listRes2;
	}	

	public static void TraspasaCHB() {
		listSatisfiables.clear();
		listUnSatisfiables.clear();

		listSatisfiables.addAll(combListBitSetStr(lBitCmbSAT));
		listUnSatisfiables.addAll(combListBitSetStr(lBitCmbUNSAT));		
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
			Collection<MClassInvariant> invClassSatisfiablesMC,
			Collection<MClassInvariant> invClassUnSatisfiablesMC,
			Collection<MClassInvariant> invClassOthersMC,
			Instant start) throws Exception {
		Instant start2 = Instant.now();
		logTime="";
		LOG.info("MVM: Analysis OCL (Greedy) - Start.");

		fmt = "%0"+String.valueOf(invClassTotal.size()).length()+"d";
		Instant end;
		Duration timeElapsed;
		String tipoSearchMSS="G";			

		// In this point We must to treat only the invariants that are satisfiables alone
		// Make col collection and strCmbTotal
		Collection<MClassInvariant> col = new ArrayList<MClassInvariant>();
		col = makeCollectionInvs(invClassSatisfiables);

		// Si cambiamos a MClassInvs seria lo siguienye (CHG)
		//		col = makeCollectionInvsMC(invClassSatisfiablesMC);

		BitSet cmbTotalHB = new BitSet();
		cmbTotalHB = makeTotalCmbCHB(col);

		CollectionBitSet resGreedyCHB = new CollectionBitSet();

		List<BitSet> listResGreedyCHB = new ArrayList<BitSet>();

		if (cmbTotalHB.size()>0) {	

			// Here We have a collection of MClassInvariant all them satisfiables
			buildTreeVisitor(col);

			// Preparation of Map of invariants with Set of invariants
			// An inv is related to another because it uses common attributes or associations
			preparaMapInfoInvSet();

			// Shows structures resulting from the Visitor
			if (showStructuresAO) {
				printStructuresAO();
			}
			Instant end2 = Instant.now();
			Duration timeElapsed2 = Duration.between(start2, end2);
			AddLogTime(".. Visitor",timeElapsed2);

			Instant start3 = Instant.now();
			// Calculate a base combination according to the Greedy method

			BitSet cmbBaseHB = new BitSet();

			// modeG = "R", random is used to start with an invariant
			// modeG = "N", random is used to start with an invariant		
			// modeG = "T" All invariants are used to join results
			String modeG="T";// Get the best results
			modeG="R";//Test
			if (debMVM) {
				LOG.info("MVM: Start Greedy");
			}

			int iIni, iFin;
			if (modeG.equals("R")) {
				iIni=0;
				iFin=1;
			}else if (modeG.equals("N")) {
				iIni=0;
				iFin=numIterGreedy; // change by number of occurrences variable obtained by parameter
			}else {
				iIni=0;
				iFin=col.size();	
			}

			for(int nInv=iIni;nInv<iFin;nInv++) {
				int nInvTratar=nInv;
				cmbBaseHB=bucleGreedyCHB(modeG, col, nInvTratar);
				resGreedyCHB.add(cmbBaseHB);
			}
			listResGreedyCHB.addAll(resGreedyCHB.getList());		

			Instant end3 = Instant.now();

			Duration timeElapsed3 = Duration.between(start3, end3);
			AddLogTime(".. Analysis OCL (Greedy1) - End",timeElapsed3);

		}

		end = Instant.now();
		timeElapsed = Duration.between(start2, end);

		// I build lists from the new structures
		TraspasaCHB();
		AddLogTime("Fin analysis_OCL (1)",timeElapsed);

		tipoSearchMSS="G";	
		int numberIter=numIterGreedy;
		Instant insShowVal1 = Instant.now();

		System.out.println("numCmbsSAT ["+numCmbsSAT+"] numCmbsUNSAT ["+numCmbsUNSAT+"] numCmbsTOTAL ["+numCmbsTOTAL+"]");

		// If the dialogue exists, we delete it.
		ValidatorMVMDialogSimple dia = MainWindow.instance().getValidatorDialog();

		if (dia!=null) {
			dia.dispose();
			MainWindow.instance().setValidatorDialog(null);
			MainWindow.instance().enableAction("ShowDiaCmb", false);
		}

		// Send to MVMDialogSimple
		ValidatorMVMDialogSimple validatorMVMDialog = showDialogMVM(
				invClassSatisfiables, 
				invClassUnSatisfiables, 
				invClassOthers,
				invClassSatisfiablesMC, 
				invClassUnSatisfiablesMC, 
				invClassOthersMC,				
				mModel,
				timeElapsed,
				tipoSearchMSS,
				numberIter,
				numCmbsTOTAL,
				numCmbsSAT,
				numCmbsUNSAT,
				false);

		validatorMVMDialog.setVisible(true);//JG
		MainWindow.instance().setValidatorDialog(validatorMVMDialog);
		MainWindow.instance().enableAction("ShowDiaCmb", true);

		Instant endShowVal1 = Instant.now();
		Duration timeShowVal1 = Duration.between(insShowVal1, endShowVal1);
		AddLogTime("Show Dialog",timeShowVal1);

		Instant endGreedy1 = Instant.now();
		Duration timeTotalGreedy1 = Duration.between(start, endGreedy1);
		AddLogTime("Total greedy1",timeTotalGreedy1);
		AddLogTime("Total Solver1",timeCallSolver);

		if (lBitCmbSAT.size()>0) {
			MainWindow.instance().enableAction("StopCalcCmb", true);
			MainWindow.instance().statusBar().showMessage("Searching for combinations using Greedy in background...");
			LanzacalculoBckCHB(listResGreedyCHB, cmbTotalHB, validatorMVMDialog, start );
		}
	}

	private void AddLogTime(String txtLog, Duration timeElapsed) {
		String textoFormateado = String.format("%-35s", txtLog);
		String numeroFormateado = String.format("%10d", timeElapsed.toMillis());
		System.out.println("[" + textoFormateado + "] ["+numeroFormateado+"]");
	}

	public EventThreads getThreadGreedy() {
		return threadGreedy;
	}

	public boolean getCalON() {
		return calON;
	}

	/**
	 * Launches the calculation of the rest of the combinations in the background
	 * @param resGreedy
	 * @param strCmbTotal
	 * @param validatorMVMDialog
	 * @param start
	 * @throws Exception
	 */

	private void LanzacalculoBckCHB(List<BitSet> listResGreedyCHB, BitSet cmbTotalCHB, ValidatorMVMDialogSimple validatorMVMDialog, 
			Instant start ) throws Exception{
		dispMVM("Background (Greedy) CH - Start.");
		Instant start4 = Instant.now();

		EventThreads hilo1 = new EventThreads(false) {

			private volatile boolean stopRequested = false;

			@Override
			public void operacionesRun() {
				dispMVM("Lanzamos operaciones en tarea background");
				try {
					threadGreedy=this;//JG
					calculateInBackGroundCHB(listResGreedyCHB, cmbTotalCHB, validatorMVMDialog, start,this );
				} catch (Exception e) {
					e.printStackTrace();
				}
			}

			public void requestStop() {
				stopRequested = true;
				this.interrupt();
			}

			public boolean isStopRequested() {
				return stopRequested;
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

				AddLogTime("LanzacalculoBckCH",timeElapsed4);
				try {
					Instant end = Instant.now();
					Duration timeElapsed = Duration.between(start, end);

					// I build lists from the new structures
					TraspasaCHB();
					validatorMVMDialog.updateInfo(listSatisfiables,listUnSatisfiables,
							timeElapsed, numCallSolver, numCallSolverSAT, numCallSolverUNSAT, numCmbsTOTAL, numCmbsSAT, numCmbsUNSAT);

					timeFinFind = Instant.now();
					timeElapsed = Duration.between(timeInitFind, timeFinFind);
					AddLogTime("Total greedy2",timeElapsed);
					AddLogTime("Total Solver2",timeCallSolver);
					// Aqui enable stop
					MainWindow.instance().enableAction("ValidationMVMG", true);
					MainWindow.instance().enableAction("ValidationMVMB", true);
					MainWindow.instance().enableAction("StopCalcCmb", false);
					threadGreedy = null;
					MainWindow.instance().statusBar().showMessage("");

				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});

		hilo1.start();
	}	

	public void stopThreadCmb() {
		if (threadGreedy!=null) {
			// see if the thread is running
			if (threadGreedy.isAlive()) {
				System.out.println("Esta vivo");

				if (threadGreedy != null) {
					threadGreedy.requestStop();
					try {
						// Wait until it finishes
						threadGreedy.join();
					} catch (InterruptedException e) {
						e.printStackTrace();
					} 
					threadGreedy = null;
				}

				//				System.out.println("lo paro");
				System.out.println("Cancellation requested. Calculation is being completed...");
				System.out.println("The calculation is complete.");
			}else {
				System.out.println("It has stopped");
			}
		}
		if (calON) {
			stopBrute=true;
		}
	}
	/**
	 * Calculation of the rest of the combinations in the background
	 * @param resGreedy
	 * @param strCmbTotal
	 * @param validatorMVMDialog
	 * @param start
	 * @throws Exception
	 */

	private void calculateInBackGroundCHB(List<BitSet> listResGreedyCHB, BitSet cmbTotalCHB, 
			ValidatorMVMDialogSimple validatorMVMDialog, Instant start, EventThreads hilo ) throws Exception {
		// Launch the bruteforce but already with greedy calculated
		lBitCmb = comRestoB(cmbTotalCHB,true, hilo);
		//aqui3
		//		MainWindow.instance().threadGreedy=(Thread) hilo;

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
	private ValidatorMVMDialogSimple showDialogMVM(
			Collection<IInvariant> invClassSatisfiables,
			Collection<IInvariant> invClassUnSatisfiables,
			Collection<IInvariant> invClassOthers,
			Collection<MClassInvariant> invClassSatisfiablesMC,
			Collection<MClassInvariant> invClassUnSatisfiablesMC,
			Collection<MClassInvariant> invClassOthersMC,			
			MModel mModel,
			Duration timeElapsed,
			String tipoSearchMSS,
			int numberIter,
			int pNumCmbsTOTAL,
			int pNumCmbsSAT,
			int pNumCmbsUNSAT,
			boolean doModal) {

		ParamDialogValidator param = new ParamDialogValidator(
				MainWindow.instance(), 
				this,
				invClassSatisfiables, 
				invClassUnSatisfiables, 
				invClassOthers,
				invClassSatisfiablesMC, 
				invClassUnSatisfiablesMC, 
				invClassOthersMC,				
				listSatisfiables,
				listUnSatisfiables,
				tabInv,
				tabInvMClass,
				mModel,
				invClassTotal,
				timeElapsed,
				numCallSolver,
				numCallSolverSAT,
				numCallSolverUNSAT,
				tipoSearchMSS,
				numberIter,
				pNumCmbsTOTAL,
				pNumCmbsSAT,
				pNumCmbsUNSAT
				);

		ValidatorMVMDialogSimple validatorMVMDialog=null;
		ValidatorMVMDialogSimple dia = MainWindow.instance().getValidatorDialog();
		if (dia!=null) {
			dia.setVisible(true);
			validatorMVMDialog=dia;
		}else {
			validatorMVMDialog= new ValidatorMVMDialogSimple(param,doModal);
			validatorMVMDialog.setVisible(true);
		}

		MainWindow.instance().enableAction("ShowDiaCmb", true);
		return validatorMVMDialog;
	}

	/**
	 * Loop to be able to call Greedy randomly or for each invariant
	 * @param modeG
	 * @param col
	 * @param iTratar
	 * @return
	 */
	private BitSet bucleGreedyCHB(String modeG, Collection<MClassInvariant> col, int iTratar) {

		BitSet cmbBaseHB = new BitSet();
		List<MClassInvariant> ic = new ArrayList<MClassInvariant>();
		colInvFault.clear();
		boolean useGreedy=true;
		while (useGreedy) {
			// Calculate the combination obtained in greedyMethod

			listCmb.clear();
			listCmbH.clear();
			listCmbB.clear();

			// ic is the list of combinations that have nothing in common
			ic = greedyMethod(modeG, col, iTratar);				

			dispMVM("Invariants collection (ic): " + ic.size());
			cmbBaseHB = new BitSet();
			for (MClassInvariant inv:ic) {
				int nCmb = searchNumInv(inv);
				if (nCmb>0) {
					cmbBaseHB.set(nCmb-1);
				}
			}

			String solucion="";
			if (debMVM) {
				LOG.info("MVM: Send to calcularGreedyCHB.");
			}

			boolean review=true;
			solucion = calcularGreedyCHB( cmbBaseHB, review,  invClassTotal);
			addSolutionGHB(cmbBaseHB, solucion);
			// if the result is UNSATISFIABLE and modeG = "R" it must be sent again to greedyMethod
			// but indicating the list of invariants that have failed in previous searches
			if (solucion.equals("SATISFIABLE")){
				useGreedy=false;
			}else {
				if (modeG.equals("R")) {
					// If it fails and the method is random, it is tried again
					// invXazar
					colInvFault.add(invXazar);
					// If the collection of inv that fail in greedyMethod is greater than or equal to
					// the list of valid invariants, we stop searching to avoid
					// infinite loops
					if (colInvFault.size()>= invClassTotal.size()) {
						useGreedy=false;
					}
				}else {
					// If the method is total (not random) it is only tried once.
					useGreedy=false;
				}
			}
		}
		return cmbBaseHB;
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

	// Si cambiamos a MClassInvs seria lo siguienye (CHG)
	//	private static Collection<MClassInvariant> makeCollectionInvsMC(Collection<MClassInvariant> invClassSatisfiables) {
	//		Collection<MClassInvariant> col = new ArrayList<MClassInvariant>();
	//		col = invClassSatisfiables;
	//		return col;
	//	}
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

	//-- possible if MClass is changed (CHG)
	//	private static int searchNumInvMC(MClassInvariant inv) {
	//		int numInvGral=-1;
	//		for (int nInv = 0; nInv < tabInvMClass.length; nInv++) {
	//			if(inv.name().equals(tabInvMClass[nInv].name())) {
	//				numInvGral=nInv+1;
	//				continue;
	//			}
	//		}
	//
	//		if (debMVM) {
	//			if (numInvGral<0) {
	//				System.out.println("inv " + inv + " numInv<0 en searchNumInv");
	//			}
	//		}
	//		return numInvGral;
	//	}
	private static int searchNumInv(IInvariant inv) {
		// Search number by inv//JG
		int numInvGral=-1;
		for (int nInv = 0; nInv < tabInv.length; nInv++) {

			if(inv.name().equals(tabInv[nInv].name()) && inv.clazz().name().equals(tabInv[nInv].clazz().name())) {
				numInvGral=nInv+1;
				break;
			}
		}
		if (debMVM) {
			if (numInvGral<0) {
				System.out.println("inv " + inv + " numInv<0 en searchNumInv");
			}
		}
		return numInvGral;
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
		System.out.println("Common attributes in related invariants");
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

		List<MClassInvariant> result = new ArrayList<MClassInvariant>();

		// col -> Total collection of satisfiable invariants

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
				// 2. Add to our combination an invariant X
				// randomly chosen within { I -> ip}.
				if (modeG.equals("R")|| modeG.equals("N")) {
					Random random = new Random();
					int nRnd = random.nextInt(n);
					invXazar = arrInv[nRnd];
					dispMVM("["+nInvTratar+"] Random hallado ["+invXazar+"]");
				}else {
					if (pVez) {
						invXazar = arrInv[nInvTratar];
						pVez=false;
					}else {
						invXazar = arrInv[0];
					}
				}
				ic.add(invXazar);

				// 3. We remove X from { I }.				
				ip.remove(invXazar);

				// 4. We consult the invariants { AND } that are related
				// (access some common element) with the invariant X.				
				Set<MClassInvariant> lInvY = new HashSet<MClassInvariant>();
				if (mapInfoInvSet.containsKey(invXazar)) {
					lInvY=mapInfoInvSet.get(invXazar);
					ip.removeAll(lInvY);
				}
			}
		}

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

	private static BitSet makeTotalCmbCHB(Collection<MClassInvariant> col) {
		BitSet cmbHB = new BitSet();
		for (MClassInvariant invClass: col) {
			int nCmb = searchNumInv(invClass);
			cmbHB.set(nCmb-1);// Tal vez deberia ser menos 1 (-1)
		}
		return cmbHB;
	}	

	/**
	 * Given a base combination obtained with greedy, look for relation of invariants
	 * remaining and returns a combination with all of them
	 * @param strCmbBase
	 * @param strCmbTotal
	 * @return
	 */

	//	private static BitSet makeRestCmbCHB(BitSet cmbBaseB, BitSet cmbTotalB) {
	//		BitSet cmbResB = (BitSet) cmbBaseB.clone();
	//		cmbResB.xor(cmbTotalB);
	//		return cmbResB;
	//	}	

	/**
	 * Print content of mapInfoInvSet
	 */
	private static void printMapInfoInvSet() {
		System.out.println();
		System.out.println("Interrelated invariants (mapInfoInvSet)");
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
		// Prepare Map of invariants with Set of invariants
		// An inv is related to another because it uses common attributes or associations
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
	 * Add solution of a combination to the list of Satisfiables or Unsatisfiables
	 * @param combinacion
	 * @param solution
	 */

	public static void addSolutionGHB(BitSet bit, String solucion) {
		numCmbsTOTAL+=1;
		if (solucion.equals("SATISFIABLE") || solucion.equals("TRIVIALLY_SATISFIABLE")) {
			lBitCmbSAT=review_store_SAT( lBitCmbSAT,  bit);		
			numCmbsSAT+=1;
		}else if (solucion.equals("UNSATISFIABLE") || solucion.equals("TRIVIALLY_UNSATISFIABLE")) {
			lBitCmbUNSAT=review_store_UNSAT( lBitCmbUNSAT,  bit);	
			numCmbsUNSAT+=1;
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
			solution = call_Solver(model);
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

	public String calcularGreedyCHB(BitSet bit, boolean bReview,Collection<IInvariant> invClassTotal) {		
		String solucion="";
		if (debMVM) {
			dispMVM("MVM: Entra en calcular (" + bit + ")");
		}

		// First of all see if you can deduce the result

		boolean calculateCH=true;		
		// See if the combination is included in a satisfiable
		// If the join is included in some satisfiable join
		// there is no need to calculate it because it will also be satisfiable	
		if (bReview) {
			calculateCH = !includedInSatisfactibleCHB(bit);
			if (!calculateCH) {
				solucion="SATISFIABLE";
				return solucion;
			}	
		}

		if (calculateCH) {
			// See if there are unsatisfiable joins that are included in the join to try 
			// If the join to try contains an unsatisfiable join, it will be unsatisfiable
			if (bReview) {
				calculateCH = !unsatisIncludedInCombinationCHB( bit);
				if (!calculateCH) {
					solucion="UNSATISFIABLE";
					return solucion;
				}	
			}
		}
		List<IInvariant> listInv = new ArrayList<IInvariant>();
		int nElem = bit.length();
		for (int i=0;i<nElem;i++) {
			if (bit.get(i)) {
				IInvariant inv = (IInvariant) tabInv[i];
				listInv.add(inv);
			}
		}		
		for (IInvariant invClass: invClassTotal) {
			if (listInv.contains(invClass)) {
				invClass.activate();
			}else {
				invClass.deactivate();
			}
		}		

		try {
			numCallSolver+=1;
			solution = call_Solver(model);
			if (solution!=null) {
				if (solution.outcome().toString() == "SATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_SATISFIABLE") {
					numCallSolverSAT+=1;
					solucion="SATISFIABLE";
				}else if (solution.outcome().toString() == "UNSATISFIABLE" || solution.outcome().toString() == "TRIVIALLY_UNSATISFIABLE") {
					numCallSolverUNSAT+=1;
					solucion="UNSATISFIABLE";
				} else {
					// do nothing
				}			
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
		// Find invariants of the combination
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

	private static boolean includedInSatisfactibleCHB(BitSet bit) {
		boolean bRes = bitIncludedInList(bit,lBitCmbSAT);
		if (bRes) {
			if (!lBitCmbSAT.contains(bit)) {
				lBitCmbSAT.add(bit);
			}
		}
		return bRes;
	}	
	/**
	 * Analiza si una combinacion esta incluida en otra
	 * @param cmbBS
	 * @param cmbContainer
	 * @return
	 */
	private static boolean bitIncludedIn(BitSet cmbBS, BitSet cmbContainer) {
		BitSet cmbBSOri=(BitSet) cmbBS.clone();		
		// Compare: is cmbBSOri include in cmbContainer?
		cmbBSOri.and(cmbContainer);
		return cmbBSOri.equals(cmbBS);
	}
	private static boolean bitIncludes(BitSet cmbContainer, BitSet cmbBS) {
		BitSet cmbBSOri=(BitSet) cmbBS.clone();		
		// Compare: is cmbContainer includes cmbBS?
		cmbBSOri.and(cmbContainer);
		return cmbBSOri.equals(cmbBS);		
	}

	private static boolean bitIncludedInList(BitSet cmbBS,List<BitSet> lBitSet) {
		boolean bRes=false;

		for (BitSet cmbBit:lBitSet) {
			BitSet cmbBSOri=(BitSet) cmbBS.clone();	
			if (bitIncludedIn(cmbBSOri, cmbBit)) {
				return true;
			}
		}
		return bRes;
	}
	private static boolean bitListIncludes(BitSet cmbBS,List<BitSet> lBitSet) {
		boolean bRes=false;

		for (BitSet cmbBit:lBitSet) {
			BitSet cmbBSOri=(BitSet) cmbBS.clone();	
			if (bitIncludes(cmbBSOri, cmbBit)) {
				bRes= true;// Disable if you want to see which ones are contained 
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
	private static boolean unsatisIncludedInCombinationCHB(BitSet bit) {
		boolean bRes = bitListIncludes(bit, lBitCmbUNSAT);
		if (bRes) {
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
