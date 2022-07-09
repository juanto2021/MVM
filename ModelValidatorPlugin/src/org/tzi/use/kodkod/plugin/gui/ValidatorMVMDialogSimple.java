package org.tzi.use.kodkod.plugin.gui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Image;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.beans.PropertyVetoException;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDesktopPane;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JInternalFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SwingConstants;
import javax.swing.border.Border;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import org.tzi.kodkod.KodkodModelValidator;
import org.tzi.kodkod.KodkodSolver;
import org.tzi.kodkod.ResInv;
import org.tzi.kodkod.model.iface.IInvariant;
import org.tzi.kodkod.model.iface.IModel;
import org.tzi.use.api.UseApiException;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.gui.main.ViewFrame;
import org.tzi.use.gui.views.diagrams.DiagramView.LayoutType;
import org.tzi.use.gui.views.diagrams.objectdiagram.NewObjectDiagramView;
import org.tzi.use.kodkod.solution.ObjectDiagramCreator;
import org.tzi.use.main.Session;
import org.tzi.use.uml.mm.MClassInvariant;
import org.tzi.use.uml.mm.MModel;

import kodkod.engine.Solution;

public class ValidatorMVMDialogSimple extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	JFrame frame;  
	String strCmbSel=null;
	String strCmb=null;
	String strCmbSAT=null;

	KodkodModelValidator kodParent=null;
	MainWindow parent=null;
	Collection<IInvariant> listInvSatisfiables = null;
	Collection<IInvariant> listInvUnSatisfiables = null;
	Collection<IInvariant> listInvOthers = null;
	Collection<IInvariant> invClassTotal=null;
	List<String> listStrSatisfiables = null;
	List<String> listStrUnSatisfiables = null;
	List<String> listStrOthers = null;
	List<String> listStrGrupos = null;

	Map<Integer, IInvariant> mapInvSAT=null;
	HashMap<String, String> mapGRP_SAT_MAX=null;
	HashMap<String, ResInv> mapInvRes=null;

	MModel mModel;
	Duration timeElapsed;
	int numCallSolver;
	int numCallSolverSAT;
	int numCallSolverUNSAT;

	JPanel p1 = null;
	JPanel p3 = null;
	JPanel pSatis = null;
	JPanel pUnSatis = null;
	JPanel pOthers = null;
	JPanel scrollImgSat = null;

	JList<String> lNames = null;
	JList<String> lNamesSat=null;
	JList<String> lNamesSol=null;
	DefaultListModel<String> lNamesInv = null;
	DefaultListModel<String> lNamesInvSat=null;
	DefaultListModel<String> lNamesInvSol=null;
	JTextArea textAreaOCL=null;
	JTextArea textAreaOCLSat=null;

	JLabel lbCmbErr=null;
	JLabel lbCmbSat=null;
	JLabel lbInvSat=null;
	JLabel lbCmbWithoutInv=null;
	JLabel lbTextOCL = null;
	JLabel lbTextOCLSat=null;

	JTabbedPane tabbedPane=null;
	JButton closeButton = null;
	JButton genGraphButton = null;
	JButton genGraphButtonD = null;
	JButton genGraphZoomButton = null;
	JButton genGraphZoomButtonD = null;	
	JLabel lbImgGraph = null;
	ImageIcon img;
	Image img1;

	int wSizeImg=170;
	int hSizeImg=170;

	int wSizeDlg=1000;
	int hSizeDlg=1000;

	String strRuta="c:\\Temp\\examples_graphviz";
	String strNomFileIn="wMVM.txt";
	String strNomFileOut="owMVM_dot.png";
	String strFileOut = strRuta + "\\" + strNomFileOut;

	public ValidatorMVMDialogSimple(final MainWindow parent, 
			KodkodModelValidator kodParent,
			Collection<IInvariant> pListInvSatisfiables, 
			Collection<IInvariant> pListInvUnSatisfiables,
			Collection<IInvariant> pListInvOthers,
			HashMap<String, String> pMapGRP_SAT_MAX,
			List<String> pListStrSatisfiables,
			List<String> pListStrUnSatisfiables,
			List<String> pListStrOthers,
			HashMap<String, ResInv> pMapInvRes,
			MModel mModel,
			Collection<IInvariant> pInvClassTotal ,
			Duration timeElapsed,
			int pNumCallSolver,
			int pNumCallSolverSAT,
			int pNumCallSolverUNSAT) {

		this.parent=parent;
		this.kodParent=kodParent;
		this.listInvSatisfiables = pListInvSatisfiables;
		this.listInvUnSatisfiables = pListInvUnSatisfiables;
		this.listInvOthers = pListInvOthers;

		this.listStrSatisfiables = sortBynNumInvs(pListStrSatisfiables,true);
		this.listStrUnSatisfiables = sortBynNumInvs(pListStrUnSatisfiables,false);
		this.listStrOthers = pListStrOthers;
		this.invClassTotal = pInvClassTotal;
		this.numCallSolver = pNumCallSolver;
		this.numCallSolverSAT = pNumCallSolverSAT;
		this.numCallSolverUNSAT = pNumCallSolverUNSAT;


		this.mapInvRes = pMapInvRes;

		List<String> sortedKeys=new ArrayList<String>(pMapGRP_SAT_MAX.keySet());
		Collections.sort(sortedKeys);
		this.listStrGrupos=sortedKeys;
		this.timeElapsed = timeElapsed;

		this.strCmbSel="";

		closeButton = new JButton("Close");
		genGraphButton = new JButton("Graph");
		genGraphButtonD = new JButton("Graph Des");
		genGraphButton.setEnabled(false);
		genGraphButtonD.setEnabled(false);
		genGraphZoomButton = new JButton("Zoom Graph");
		genGraphZoomButton.setEnabled(false);
		genGraphZoomButtonD = new JButton("Zoom Graph Des");
		genGraphZoomButtonD.setEnabled(false);

		lbCmbErr = new JLabel("CMB: xxx", SwingConstants.CENTER);
		lbCmbWithoutInv = new JLabel("Example instances without inv.: xxx", SwingConstants.CENTER);
		lbTextOCL = new JLabel("OCL for inv.: ---", SwingConstants.CENTER);
		lbTextOCLSat = new JLabel("OCL for inv.: ---", SwingConstants.CENTER);

		mapInvSAT = new HashMap<>();
		mapGRP_SAT_MAX = pMapGRP_SAT_MAX;
		int i = 0;
		for (IInvariant invClass: listInvSatisfiables) {
			i+=1;
			mapInvSAT.put(i, invClass);
		}

		this.mModel=mModel;
		frame = new JFrame("Validator with combinations");

		//JG Cambiar url resource MvMJG.png

		Image icono = Toolkit.getDefaultToolkit().getImage("C:\\Users\\Juanto\\git\\JuantoModelValidator\\ModelValidatorPlugin\\resources\\MvMJG.png");
		frame.setIconImage(icono);

		frame.setSize(900, 400);
		frame.setVisible(true);
		frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE); 
		frame.getContentPane().setLayout(new BorderLayout());

		JPanel p = new JPanel();
		p.setLayout(new BorderLayout());


		tabbedPane = new JTabbedPane(JTabbedPane.TOP);
		pack();

		// LANZATAB
		tabbedPane.addTab("Errors", makeErrores(listStrUnSatisfiables,"Errors"));
		tabbedPane.addTab("Best approximate solutions ", makeSolutions(listStrSatisfiables,"Best approximate solutions "));
		tabbedPane.addTab("Statistics ", makeStatistics("Statistics "));

		tabbedPane.addChangeListener(new ChangeListener() {

			@Override
			public void stateChanged(ChangeEvent e) {
				genGraphButton.setEnabled(tabbedPane.getSelectedIndex()==2);
				genGraphButtonD.setEnabled(tabbedPane.getSelectedIndex()==2);
				genGraphZoomButton.setEnabled(tabbedPane.getSelectedIndex()==2);
				genGraphZoomButtonD.setEnabled(tabbedPane.getSelectedIndex()==2);
			}
		});

		p.add(tabbedPane,BorderLayout.CENTER);

		p.add(makeBottom(), BorderLayout.SOUTH);

		frame.getContentPane().add(p);
		frame.setMinimumSize(new Dimension(getWidth(), getHeight()));
		frame.setLocationRelativeTo(this);
		frame.setEnabled(true);
	}

	private JPanel makeBottom() {
		p3 = new JPanel();
		p3.setLayout(new FlowLayout(FlowLayout.CENTER));

		closeButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				frame.dispose();
			}
		});

		p3.add(closeButton);
		return p3;
	}
	/**
	 * order the combinations so that the ones with the most invariance are found in the first positions
	 * @param listaIn
	 * @param descending
	 * @return
	 */

	private List<String> sortBynNumInvs(List<String> listaIn, boolean descending){
		List<String> listaOut=new ArrayList<String>();
		Map<String, String> mapSort = new HashMap<>();;
		for (String strSAT: listaIn) {
			String[] partes = strSAT.split("-");
			int nPartes = partes.length;
			int orden=0;
			if (descending) {
				orden = 10000-nPartes;
			}else {
				orden = nPartes;
			}

			String strValorfmt = String.format("%5s", orden).replace(' ', '0');
			String strValor=strValorfmt + " " + strSAT;
			mapSort.put(strValor,strSAT);			

		}

		List<Entry<String, String>> listOrder = new ArrayList<>(mapSort.entrySet());
		listOrder.sort(Entry.comparingByKey());

		for (int i = 0; i < listOrder.size(); i++) {
			String valor = listOrder.get(i).getKey();
			String[] partes = valor.split(" ");
			String cmb = partes[1];
			listaOut.add(cmb);
		}
		return listaOut;
	}

	private DefaultListModel<String> makeListMode(List<String> aux) {
		DefaultListModel<String> ldefLModel = new DefaultListModel<String>();
		for (String nameInv: aux) {
			String strLineList = nameInv;
			ldefLModel.addElement(strLineList);
		}

		return ldefLModel;
	}
	/**
	 * Obtiene la definicion OCL para una invariante
	 * @param strNameInv
	 * @return
	 */
	private String getOCL(String strNameInv) {
		String descInvs="";
		if (mapInvRes.containsKey(strNameInv)) {
			for (MClassInvariant invariant: mModel.classInvariants()) {
				String strInvariant = invariant.cls().name()+"::"+invariant.name();
				if (strInvariant.equals(strNameInv)) {
					descInvs=strNameInv;
					descInvs+="\n   "+invariant.bodyExpression().toString();
				}
			}

		}		
		return descInvs;
	}
	/**
	 * Devuelve la lista de invariantes de una combinacion
	 * @param cmb
	 * @return
	 */
	private List<String> getListInv(String cmb){
		//		System.out.println("Entra cmb " + cmb);
		List<String> lNInv = new ArrayList<String>();
		if (cmb.equals("")) {
			return lNInv;
		}
		String[] partes = cmb.split("-");		
		int numPartes=partes.length;
		for (int nParte = 0 ; nParte < numPartes ; nParte++) {
			String nInv = partes[nParte];
			int order = Integer.parseInt(nInv);
			boolean hallado=false;

			for (Map.Entry<String, ResInv> entry : mapInvRes.entrySet()) {
				if (!hallado) {
					ResInv invRes = (ResInv) entry.getValue();
					if (invRes.getIntOrden()==order) {
						lNInv.add(invRes.getStrInv());
						hallado=true;
					}
				}
			}			
		}

		return lNInv;
	}
	/**
	 * Busca combinaciones satisfiables sin la invariante indicada
	 * @param cmb
	 * @return
	 */
	private List<String> getCmbSinInv(String inv){
		List<String> lCmbSinInv = new ArrayList<String>();
		if (inv.equals("")) {
			return lCmbSinInv;
		}
		try {

			// Busca el numero de orden de la invariante
			int orden = -1;
			if (mapInvRes.containsKey(inv)) {
				ResInv invRes = (ResInv) mapInvRes.get(inv);
				orden=invRes.getIntOrden();
			}			

			// Buscar combinaciones satisfiables que no tengan esa invariante
			for (String strSAT: listStrSatisfiables) {
				String[] partes = strSAT.split("-");
				int numPartes=partes.length;
				boolean esta = false;
				for (int nParte = 0 ; nParte < numPartes ; nParte++) {
					String parte = partes[nParte];
					if (String.valueOf(orden).equals(parte)) {
						esta=true;
					}
				}
				if (!esta) {
					lCmbSinInv.add(strSAT);
				}

			}
		}
		catch(Exception e) {
			//  Block of code to handle errors
			return lCmbSinInv;
		}

		return lCmbSinInv;
	}
	/**
	 * Verifica si la combinacion A se halla dentro de la combinacion B
	 * @param cmbA
	 * @param cbmB
	 * @return
	 */
	private boolean checkAinsideB(String cmbA,String cmbB) {
		//		System.out.println("Se mira a ver si "+cmbA+ " esta en "+cmbB);
		boolean res=true;
		int totalInv = listInvSatisfiables.size() + listInvUnSatisfiables.size() ;

		String strFormat="%0"+String.valueOf(totalInv).length()+"d";

		Map<String,String> mapResLimpia = new HashMap<>();
		String[] partesA = cmbA.split("-");
		int numPartesA=partesA.length;
		for (int nParteA = 0 ; nParteA < numPartesA ; nParteA++) {
			String parteA = partesA[nParteA];

			String strparteA = String.format(strFormat,Integer.parseInt(parteA));

			mapResLimpia.put(strparteA, "N");
			String[] partes = cmbB.split("-");
			int numPartes=partes.length;
			for (int nParte = 0 ; nParte < numPartes ; nParte++) {
				String parteB = partes[nParte];
				//				String strparteB = String.format(strFormat,parteB);
				String strparteB = String.format(strFormat,Integer.parseInt(parteB));
				if (strparteA.equals(strparteB)) {
					if (mapResLimpia.containsKey(strparteB)) {
						mapResLimpia.put(strparteB, "S");
					}
				}
			}			
		}
		// Se analiza si todas las partes de la combinacion A estan en la combinacion B

		for (Map.Entry<String, String> entry : mapResLimpia.entrySet()) {
			String comparacion = (String) entry.getValue();
			if (comparacion.equals("N")) {
				res=false;
			}
		}				

		return res;
	}

	private List<String> limpiaUNSAT(){
		List<String> lUNSATLimpia = new ArrayList<String>();
		for (String strCmbUNSAT: listStrUnSatisfiables) {
			//			System.out.println("Se analiza " + strCmbUNSAT);

			boolean guardar = true;
			for (String strCmbLimpia: lUNSATLimpia) {

				// Se mira a ver si la combinacion 'lim pia' (o sea nucleo) esta en la combinacion a analizar 
				boolean limpiaIncluida = checkAinsideB(strCmbLimpia,strCmbUNSAT) ;

				// Si halla una combinacion incluida, ya no se guarda
				if (limpiaIncluida) {
					guardar=false;
				}
			}
			if (guardar) {
				lUNSATLimpia.add(strCmbUNSAT);
				continue;
			}	
		}
		return lUNSATLimpia;
	}

	private List<String> limpiaSAT(List<String> listaCmbs){
		List<String> lSATLimpia = new ArrayList<String>();
		for (String strCmbSAT: listaCmbs) {

			boolean guardar = true;
			for (String strCmbLimpia: lSATLimpia) {
				// Se mira a ver si la combinacion 'limpia' (o sea nucleo) esta en la combinacion a analizar 
				boolean limpiaIncluida = checkAinsideB(strCmbSAT,strCmbLimpia) ;

				// Si halla una combinacion incluida, ya no se guarda
				if (limpiaIncluida) {
					guardar=false;
				}
			}
			if (guardar) {
				lSATLimpia.add(strCmbSAT);
				continue;
			}	
		}
		return lSATLimpia;
	}


	private JPanel makeErrores(List<String> listStr, String nomTab) {
		Border border;
		border = BorderFactory.createLineBorder(Color.BLUE);

		JPanel pTotal = new JPanel();
		pTotal.setLayout(new BorderLayout());

		JPanel pSup = new JPanel();
		pSup.setLayout(new BoxLayout(pSup,BoxLayout.X_AXIS));
		pSup.setBorder(border);

		JPanel pInf = new JPanel();
		pInf.setLayout(new BoxLayout(pInf,BoxLayout.X_AXIS));
		pInf.setBorder(border);

		// Faulty combinations		
		JPanel pListCmbErr = new JPanel();
		pListCmbErr.setBorder(border);
		pListCmbErr.setLayout(new BorderLayout());

		// Hacer limpieza de combinaciones insatisfactibles que ya contengan combinaciones insatisfactibles menores
		List<String> listStrUNSATLimpia = limpiaUNSAT();

		// Lista con combinaciones insatisfactibles
		DefaultListModel<String> lUNSAT = makeListMode(listStrUNSATLimpia);

		JList<String> lCombis = new JList<String>(lUNSAT);

		JScrollPane scrollPane = new JScrollPane (lCombis,    JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
				JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED); 
		lCombis.setSelectedIndex(0);
		strCmb="";
		if (lUNSAT.size()>0) {
			strCmb = lCombis.getSelectedValue().trim();
		}

		lCombis.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {
				strCmb = lCombis.getSelectedValue().trim();
				lbCmbErr.setText(strCmb);
				lNamesInv = new DefaultListModel<String>();
				for (String nameInv: getListInv(strCmb)) {
					String strLineList = nameInv;
					lNamesInv.addElement(strLineList);
				}
				lNames.setModel(lNamesInv);
				lNames.setSelectedIndex(0);

				String valor = lNames.getSelectedValue().trim();
				int orden = -1;
				if (mapInvRes.containsKey(valor)) {
					ResInv invRes = (ResInv) mapInvRes.get(valor);
					orden=invRes.getIntOrden();
				}
				lbCmbWithoutInv.setText("Example instances without inv.: " + valor+ " ("+orden+")");
				lbTextOCL.setText("OCL for inv.: " + valor);

				String textOCL = getOCL(lNames.getSelectedValue().trim());
				textAreaOCL.setText(textOCL);
				textAreaOCL.setCaretPosition(0);

				DefaultListModel<String> lCmbs = new DefaultListModel<String>();
				if (lNamesInv.size()>0) {
					String elementSelected = lNames.getSelectedValue().trim();
					List<String> listStrCMbLimpia = new ArrayList<String>();
					listStrCMbLimpia= limpiaSAT(getCmbSinInv(elementSelected));
					for (String cmb: listStrCMbLimpia) {
						lCmbs.addElement(cmb);
					}		
					listStrCMbLimpia = limpiaSAT(getCmbSinInv(elementSelected));
				}		
				lNamesSat.setModel(lCmbs);

			}
		});

		JLabel lbFaultCmb = new JLabel("Faulty combinations", SwingConstants.CENTER);
		pListCmbErr.add(lbFaultCmb,BorderLayout.NORTH);
		pListCmbErr.add(scrollPane, BorderLayout.CENTER);

		// Combination in course previously selected
		JPanel pListInvCmbErr = new JPanel();
		pListInvCmbErr.setBorder(border);
		pListInvCmbErr.setLayout(new BorderLayout());

		// Lista con nombres de invariantes de combinaciones insatisfactibles
		lNamesInv = new DefaultListModel<String>();

		for (String nameInv: getListInv(strCmb)) {
			String strLineList = nameInv;
			lNamesInv.addElement(strLineList);
		}

		lNames = new JList<String>(lNamesInv);

		JScrollPane scrollPaneName = new JScrollPane (lNames,    JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
				JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED); 

		// Evento clic
		lNames.setSelectedIndex(0);
		lNames.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {
				String valor = lNames.getSelectedValue().trim();
				int orden = -1;
				if (mapInvRes.containsKey(valor)) {
					ResInv invRes = (ResInv) mapInvRes.get(valor);
					orden=invRes.getIntOrden();
				}
				lbCmbWithoutInv.setText("Example instances without inv.: " + valor+ " ("+orden+")");
				lbTextOCL.setText("OCL for inv.: " + valor);
				String textOCL = getOCL(lNames.getSelectedValue().trim());
				textAreaOCL.setText(textOCL);
				textAreaOCL.setCaretPosition(0);

				DefaultListModel<String> lCmbs = new DefaultListModel<String>();
				if (lNamesInv.size()>0) {
					String elementSelected = lNames.getSelectedValue().trim();
					List<String> listStrCMbLimpia = new ArrayList<String>();
					listStrCMbLimpia= limpiaSAT(getCmbSinInv(elementSelected));
					for (String cmb: listStrCMbLimpia) {
						lCmbs.addElement(cmb);
					}		
					listStrCMbLimpia = limpiaSAT(getCmbSinInv(elementSelected));
				}

				lNamesSat.setModel(lCmbs);

			}
		});
		lbCmbErr.setText(strCmb);
		pListInvCmbErr.add(lbCmbErr,BorderLayout.NORTH);
		pListInvCmbErr.add(scrollPaneName, BorderLayout.CENTER);	

		// Combinations without the invariant without error	
		JPanel pListInvCmbSinErr = new JPanel();
		pListInvCmbSinErr.setBorder(border);
		pListInvCmbSinErr.setLayout(new BorderLayout());


		DefaultListModel<String> lCmbs = new DefaultListModel<String>();
		if (lNamesInv.size()>0) {
			String elementSelected = lNames.getSelectedValue().trim();
			List<String> listStrCMbLimpia = new ArrayList<String>();
			listStrCMbLimpia= limpiaSAT(getCmbSinInv(elementSelected));
			for (String cmb: listStrCMbLimpia) {
				lCmbs.addElement(cmb);
			}		
			listStrCMbLimpia = limpiaSAT(getCmbSinInv(elementSelected));
		}

		// Se ha de limpiar la lista de cmbs para noi incluir las superfluas
		lNamesSat = new JList<String>(lCmbs);

		lNamesSat.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {

				String combinacion = lNamesSat.getSelectedValue().trim();
				if (evt.getClickCount() == 2 && evt.getButton() == MouseEvent.BUTTON1) {

					Solution solution=null;
					KodkodSolver kodkodSolver = new KodkodSolver();
					try {
						solution = kodParent.calcular( combinacion,  invClassTotal,  kodkodSolver);
						if (solution.outcome().toString() == "SATISFIABLE") {
							Session session = kodParent.getSession();
							try {
								createObjectDiagramCreator(combinacion, solution,kodParent.getIModel(),  session);
							} catch (Exception e) {
								e.printStackTrace();
							}
						}else {
							String st = "Unsatisfactory combinations don't create object diagram!!";
							JOptionPane.showMessageDialog(null, st);
						}

					} catch (Exception e) {
						e.printStackTrace();
					}
				}				
			}
		});


		JScrollPane scrollPaneNameSat = new JScrollPane (lNamesSat,    JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
				JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED); 

		pListInvCmbSinErr.add(lbCmbWithoutInv,BorderLayout.NORTH);
		pListInvCmbSinErr.add(scrollPaneNameSat, BorderLayout.CENTER);			


		pSup.add(pListCmbErr);
		pSup.add(pListInvCmbErr);
		pSup.add(pListInvCmbSinErr);

		// Code OCL of the invariant selected		
		JPanel pOCLCode = new JPanel();
		pOCLCode.setBorder(border);
		pOCLCode.setLayout(new BorderLayout());		
		textAreaOCL= new JTextArea();
		String textOCL = "";
		if (lNamesInv.size()>0) {
			textOCL = getOCL(lNames.getSelectedValue().trim());
		}

		textAreaOCL.setText(textOCL);
		textAreaOCL.setCaretPosition(0);
		final JScrollPane scrollPaneTA = new JScrollPane(textAreaOCL,
				JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
				JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		scrollPaneTA.getVerticalScrollBar().setValue(0); // scroll to the top

		if (lNamesInv.size()>0) {
			String valor = lNames.getSelectedValue().trim();
			int orden = -1;
			if (mapInvRes.containsKey(valor)) {
				ResInv invRes = (ResInv) mapInvRes.get(valor);
				orden=invRes.getIntOrden();
			}
			lbCmbWithoutInv.setText("Example instances without inv.: " + valor+ " ("+orden+")");		
		}else {
			lbCmbWithoutInv.setText("Example instances without inv.: ");
		}

		pOCLCode.add(lbTextOCL,BorderLayout.NORTH);
		pOCLCode.add(scrollPaneTA, BorderLayout.CENTER);
		pInf.add(pOCLCode);

		pTotal.add(pSup, BorderLayout.NORTH);
		pTotal.add(pInf,BorderLayout.CENTER);

		return pTotal;
	}
	private JPanel makeSolutions(List<String> listStr, String nomTab) {
		Border border;
		border = BorderFactory.createLineBorder(Color.BLUE);

		JPanel pTotal = new JPanel();
		pTotal.setLayout(new BorderLayout());

		JPanel pSup = new JPanel();
		pSup.setLayout(new BoxLayout(pSup,BoxLayout.X_AXIS));
		pSup.setBorder(border);

		JPanel pInf = new JPanel();
		pInf.setLayout(new BoxLayout(pInf,BoxLayout.X_AXIS));
		pInf.setBorder(border);

		// Best approximate solutions 
		JPanel pListCmbSat = new JPanel();
		pListCmbSat.setBorder(border);
		pListCmbSat.setLayout(new BorderLayout());

		// Hacer limpieza de combinaciones insatisfactibles que ya contengan combinaciones insatisfactibles menores
		List<String> listStrSATLimpia = limpiaSAT(listStrSatisfiables);

		// Lista con combinaciones satisfactibles 'limpias' de combinaciones superfluas
		DefaultListModel<String> lSAT = makeListMode(listStrSATLimpia);

		JList<String> lCombis = new JList<String>(lSAT);

		JScrollPane scrollPane = new JScrollPane (lCombis,    JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
				JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED); 
		lCombis.setSelectedIndex(0);
		strCmbSAT="";
		if (lSAT.size()>0) {
			strCmbSAT = lCombis.getSelectedValue().trim();
		}

		lCombis.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {
				strCmbSAT = lCombis.getSelectedValue().trim();
				lbInvSat.setText(strCmbSAT);
				lNamesInvSol = new DefaultListModel<String>();
				for (String nameInv: getListInv(strCmbSAT)) {
					String strLineList = nameInv;

					lNamesInvSol.addElement(strLineList);
				}
				lNamesSol.setModel(lNamesInvSol);
				lNamesSol.setSelectedIndex(0);

				String valor = lNamesSol.getSelectedValue().trim();

				lbTextOCLSat.setText("OCL for inv.: " + valor);

				String textOCL = getOCL(lNamesSol.getSelectedValue().trim());
				textAreaOCLSat.setText(textOCL);
				textAreaOCLSat.setCaretPosition(0);
				// Crear object diagram
				
				if (evt.getClickCount() == 2 && evt.getButton() == MouseEvent.BUTTON1) {

					Solution solution=null;
					KodkodSolver kodkodSolver = new KodkodSolver();
					try {
						solution = kodParent.calcular( strCmbSAT,  invClassTotal,  kodkodSolver);
						if (solution.outcome().toString() == "SATISFIABLE") {
							Session session = kodParent.getSession();
							try {
								createObjectDiagramCreator(strCmbSAT, solution,kodParent.getIModel(),  session);
							} catch (Exception e) {
								e.printStackTrace();
							}
						}else {
							String st = "Unsatisfactory combinations don't create object diagram!!";
							JOptionPane.showMessageDialog(null, st);
						}

					} catch (Exception e) {
						e.printStackTrace();
					}
				}					
				//				
			}
		});


		lbCmbSat = new JLabel("Invariants", SwingConstants.CENTER);
		pListCmbSat.add(lbCmbSat,BorderLayout.NORTH);
		pListCmbSat.add(scrollPane, BorderLayout.CENTER);

		// Combination in course previously selected
		JPanel pListInvCmbSat = new JPanel();
		pListInvCmbSat.setBorder(border);
		pListInvCmbSat.setLayout(new BorderLayout());

		// Lista con nombres de invariantes de combinaciones satisfactibles
		lNamesInvSol = new DefaultListModel<String>();

		for (String nameInv: getListInv(strCmbSAT)) {
			String strLineList = nameInv;
			lNamesInvSol.addElement(strLineList);
		}

		lNamesSol = new JList<String>(lNamesInvSol);

		JScrollPane scrollPaneName = new JScrollPane (lNamesSol,    JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
				JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED); 

		// Evento clic
		lNamesSol.setSelectedIndex(0);
		lNamesSol.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {
				String valor = lNamesSol.getSelectedValue().trim();
				lbTextOCLSat.setText("OCL for inv.: " + valor);
				String textOCL = getOCL(lNamesSol.getSelectedValue().trim());
				textAreaOCLSat.setText(textOCL);
				textAreaOCLSat.setCaretPosition(0);
			}
		});
		lbInvSat = new JLabel(strCmbSAT, SwingConstants.CENTER);
		pListInvCmbSat.add(lbInvSat,BorderLayout.NORTH);
		pListInvCmbSat.add(scrollPaneName, BorderLayout.CENTER);	

		pSup.add(pListCmbSat);
		pSup.add(pListInvCmbSat);

		// Code OCL of the invariant selected		
		JPanel pOCLCode = new JPanel();
		pOCLCode.setBorder(border);
		pOCLCode.setLayout(new BorderLayout());		
		textAreaOCLSat= new JTextArea();
		String textOCL = "";

		if (lNamesInvSol.size()>0) {
			textOCL = getOCL(lNamesSol.getSelectedValue().trim());
		}

		textAreaOCLSat.setText(textOCL);
		textAreaOCLSat.setCaretPosition(0);
		final JScrollPane scrollPaneTA = new JScrollPane(textAreaOCLSat,
				JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED,
				JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		scrollPaneTA.getVerticalScrollBar().setValue(0); // scroll to the top

		pOCLCode.add(lbTextOCLSat,BorderLayout.NORTH);
		pOCLCode.add(scrollPaneTA, BorderLayout.CENTER);
		pInf.add(pOCLCode);

		pTotal.add(pSup, BorderLayout.NORTH);
		pTotal.add(pInf,BorderLayout.CENTER);

		return pTotal;
	}
	private JPanel makeStatistics(String nomTab) {
		Border border;
		border = BorderFactory.createLineBorder(Color.BLUE);

		JPanel pTotal = new JPanel();
		pTotal.setLayout(new BorderLayout());

		JPanel pSup = new JPanel();
		pSup.setLayout(new BoxLayout(pSup,BoxLayout.Y_AXIS));
		pSup.setBorder(border);

		JPanel pDatos1 = new JPanel();
		JPanel pDatos2 = new JPanel();
		JPanel pDatos3 = new JPanel();
		JPanel pDatos4 = new JPanel();
		JPanel pDatos5 = new JPanel();
		JPanel pDatos6 = new JPanel();	
		JPanel pDatos7 = new JPanel();	
		pDatos1.setLayout(new FlowLayout(FlowLayout.LEFT));
		pDatos2.setLayout(new FlowLayout(FlowLayout.LEFT));
		pDatos3.setLayout(new FlowLayout(FlowLayout.LEFT));
		pDatos4.setLayout(new FlowLayout(FlowLayout.LEFT));
		pDatos5.setLayout(new FlowLayout(FlowLayout.LEFT));
		pDatos6.setLayout(new FlowLayout(FlowLayout.LEFT));
		pDatos7.setLayout(new FlowLayout(FlowLayout.LEFT));

		Dimension dl = new Dimension();
		dl.width=220;
		dl.height=20;

		Dimension dt = new Dimension();
		dt.width=160;
		dt.height=20;

		// Execution time
		JLabel lbTime = new JLabel("Execution time ");
		lbTime.setPreferredSize(dl);

		long time = timeElapsed.toMillis();
		String strTime = time +" milliseconds";

		JTextField txTime = new JTextField(strTime); 
		txTime.setPreferredSize(dt);
		txTime.setEditable(false);
		txTime.setHorizontalAlignment(JTextField.RIGHT);

		pDatos1.add(lbTime,BorderLayout.NORTH);
		pDatos1.add(txTime,BorderLayout.NORTH);

		// Llamadas al Solver
		JLabel lbNumCalls = new JLabel("Number of calls to the solver ");
		lbNumCalls.setPreferredSize(dl);

		JTextField txNumCalls = new JTextField(String.valueOf(numCallSolver)); 
		txNumCalls.setPreferredSize(dt);
		txNumCalls.setEditable(false);
		txNumCalls.setHorizontalAlignment(JTextField.RIGHT);

		pDatos2.add(lbNumCalls,BorderLayout.NORTH);
		pDatos2.add(txNumCalls,BorderLayout.NORTH);

		// Number of satisfied calls
		JLabel lbNumCallsSAT = new JLabel("Number of satisfied calls ");
		lbNumCallsSAT.setPreferredSize(dl);

		JTextField txNumCallsSAT = new JTextField(String.valueOf(numCallSolverSAT)); 
		txNumCallsSAT.setPreferredSize(dt);
		txNumCallsSAT.setEditable(false);
		txNumCallsSAT.setHorizontalAlignment(JTextField.RIGHT);

		pDatos3.add(lbNumCallsSAT,BorderLayout.NORTH);
		pDatos3.add(txNumCallsSAT,BorderLayout.NORTH);		

		// Number of unsatisfiable calls
		JLabel lbNumCallsUNSAT = new JLabel("Number of unsatisfied calls ");
		lbNumCallsUNSAT.setPreferredSize(dl);

		JTextField txNumCallsUNSAT = new JTextField(String.valueOf(numCallSolverUNSAT)); 
		txNumCallsUNSAT.setPreferredSize(dt);
		txNumCallsUNSAT.setEditable(false);
		txNumCallsUNSAT.setHorizontalAlignment(JTextField.RIGHT);

		pDatos4.add(lbNumCallsUNSAT,BorderLayout.NORTH);
		pDatos4.add(txNumCallsUNSAT,BorderLayout.NORTH);		

		// Number total of combinations
		JLabel lbNumCmbTotal = new JLabel("Total number of combinations ");
		lbNumCmbTotal.setPreferredSize(dl);

		JTextField txNumCmbTotal = new JTextField(Integer.toString(listStrSatisfiables.size()+listStrUnSatisfiables.size())); 
		txNumCmbTotal.setPreferredSize(dt);
		txNumCmbTotal.setEditable(false);
		txNumCmbTotal.setHorizontalAlignment(JTextField.RIGHT);

		pDatos5.add(lbNumCmbTotal,BorderLayout.NORTH);
		pDatos5.add(txNumCmbTotal,BorderLayout.NORTH);	

		// Number total of combinations satisfiables
		JLabel lbNumCmbSAT = new JLabel("Total number of combinations satisfiable ");
		lbNumCmbSAT.setPreferredSize(dl);

		JTextField txNumCmbSAT = new JTextField(Integer.toString(listStrSatisfiables.size())); 
		txNumCmbSAT.setPreferredSize(dt);
		txNumCmbSAT.setEditable(false);
		txNumCmbSAT.setHorizontalAlignment(JTextField.RIGHT);

		pDatos6.add(lbNumCmbSAT,BorderLayout.NORTH);
		pDatos6.add(txNumCmbSAT,BorderLayout.NORTH);			

		// Number total of combinations unsatisfiables
		JLabel lbNumCmbUNSAT = new JLabel("Total number of combinations unsatisfiable ");
		lbNumCmbUNSAT.setPreferredSize(dl);

		JTextField txNumCmbUNSAT = new JTextField(Integer.toString(listStrUnSatisfiables.size())); 
		txNumCmbUNSAT.setPreferredSize(dt);
		txNumCmbUNSAT.setEditable(false);
		txNumCmbUNSAT.setHorizontalAlignment(JTextField.RIGHT);

		pDatos7.add(lbNumCmbUNSAT,BorderLayout.NORTH);
		pDatos7.add(txNumCmbUNSAT,BorderLayout.NORTH);	

		pSup.add(pDatos1);
		pSup.add(pDatos2);
		pSup.add(pDatos3);
		pSup.add(pDatos4);
		pSup.add(pDatos5);
		pSup.add(pDatos6);
		pSup.add(pDatos7);
		pTotal.add(pSup, BorderLayout.NORTH);
		return pTotal;
	}

	private void createObjectDiagramCreator(String combinacion, Solution solution,IModel iModel, Session session) {
		ObjectDiagramCreator odc = new ObjectDiagramCreator(kodParent.getIModel(), session);// IModel, session	
		try {
			odc.create(solution.instance().relationTuples());
		} catch (UseApiException e) {
			e.printStackTrace();
		}

		NewObjectDiagramView odv = new NewObjectDiagramView(parent, session.system());
		ViewFrame f = new ViewFrame("Object diagram ("+combinacion+")", odv, "ObjectDiagram.gif");
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
		odv.getDiagram().startLayoutFormatThread(LayoutType.HierarchicalUpsideDown, hSpace, vSpace, rootPaneCheckingEnabled);

		parent.addNewViewFrame(f);
		parent.getObjectDiagrams().add(odv);

		tile();
		odv.getDiagram().startLayoutFormatThread(LayoutType.HierarchicalUpsideDown, hSpace, vSpace, rootPaneCheckingEnabled);

	}

	private void tile() {
		JDesktopPane fDesk = parent.getFdesk();
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
}
