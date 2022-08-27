package org.tzi.use.kodkod.plugin.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.Image;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.beans.PropertyVetoException;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

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
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import org.tzi.kodkod.KodkodModelValidator;
import org.tzi.kodkod.KodkodSolver;
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

public class ValidatorMVMDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	JFrame frame;  
	String strCmbSel=null;

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

	MModel mModel;
	Duration timeElapsed;

	JPanel p1 = null;
	JPanel p3 = null;
	JPanel pSatis = null;
	JPanel pUnSatis = null;
	JPanel pOthers = null;
	JPanel scrollImgSat = null;
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

	int wSizeDlg=1200;
	int hSizeDlg=700;

	String strRuta="c:\\Temp\\examples_graphviz";
	String strNomFileIn="wMVM.txt";
	String strNomFileOut="owMVM_dot.png";
	String strFileOut = strRuta + "\\" + strNomFileOut;

	public ValidatorMVMDialog(final MainWindow parent, 
			KodkodModelValidator kodParent,
			Collection<IInvariant> pListInvSatisfiables, 
			Collection<IInvariant> pListInvUnSatisfiables,
			Collection<IInvariant> pListInvOthers,
			HashMap<String, String> pMapGRP_SAT_MAX,
			List<String> pListStrSatisfiables,
			List<String> pListStrUnSatisfiables,
			List<String> pListStrOthers,
			MModel mModel,
			Collection<IInvariant> pInvClassTotal ,
			Duration timeElapsed) {

		this.parent=parent;
		this.kodParent=kodParent;
		this.listInvSatisfiables = pListInvSatisfiables;
		this.listInvUnSatisfiables = pListInvUnSatisfiables;
		this.listInvOthers = pListInvOthers;

		this.listStrSatisfiables = sortBynNumInvs(pListStrSatisfiables,true);
		this.listStrUnSatisfiables = sortBynNumInvs(pListStrUnSatisfiables,false);
		this.listStrOthers = pListStrOthers;
		this.invClassTotal = pInvClassTotal;

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

		mapInvSAT = new HashMap<>();
		mapGRP_SAT_MAX = pMapGRP_SAT_MAX;
		int i = 0;
		for (IInvariant invClass: listInvSatisfiables) {
			i+=1;
			mapInvSAT.put(i, invClass);
		}

		this.mModel=mModel;
		frame = new JFrame("Validator con combinaciones");

		//JG Cambiar url resource MvMJG.png

		Image icono = Toolkit.getDefaultToolkit().getImage("C:\\Users\\Juanto\\git\\JuantoModelValidator\\ModelValidatorPlugin\\resources\\MvMJG.png");
		frame.setIconImage(icono);

		frame.setSize(900, 320);
		frame.setVisible(true);
		frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE); 
		frame.getContentPane().setLayout(new BorderLayout());

		JPanel p = new JPanel();
		p.setLayout(new BorderLayout());

		p.add(makeComun(listStrSatisfiables.size() , listStrUnSatisfiables.size(), timeElapsed),BorderLayout.NORTH);

		tabbedPane = new JTabbedPane(JTabbedPane.TOP);
		pack();

		tabbedPane.addTab("Satisfiables uni", make1(listInvSatisfiables,true));
		tabbedPane.addTab("UnSatisfiables uni.", make1(listInvUnSatisfiables,false));
		pSatis = makeCombi(listStrSatisfiables,"SAT");
		tabbedPane.addTab("Satisfiables comb.", pSatis);
		pUnSatis = makeCombi(listStrUnSatisfiables,"UNSAT");
		tabbedPane.addTab("UnSatisfiables comb.", pUnSatis);
		pOthers = makeCombi(listStrOthers,"OTHERS");
		tabbedPane.addTab("Others comb.", pOthers);
		tabbedPane.addTab("Ranking Comb. Satisf.", makeRanking());
		tabbedPane.addTab("Grupos", makeRankingGrupos(mapGRP_SAT_MAX));

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
	private JPanel makeComun(int nSAT, int nUNSAT, Duration timeElapsed) {
		p1 = new JPanel();
		p1.setLayout(new FlowLayout(FlowLayout.LEFT));
		Dimension d = new Dimension();
		d.height=30;
		p1.setPreferredSize(d);

		JLabel idLabelNC = new JLabel("Num. combinaciones: ");
		JTextField idNC = new JTextField(Integer.toString(listStrSatisfiables.size()+listStrUnSatisfiables.size())); 
		d = new Dimension();
		d.width=40;
		d.height=20;
		idNC.setPreferredSize(d);
		idNC.setEditable(false);
		idNC.setHorizontalAlignment(JTextField.RIGHT);

		JLabel idLabelSAT = new JLabel("Satisfiables: ");
		JTextField idSAT = new JTextField(Integer.toString(listStrSatisfiables.size())); 
		idSAT.setPreferredSize(d);
		idSAT.setEditable(false);
		idSAT.setHorizontalAlignment(JTextField.RIGHT);

		JLabel idLabelUNSAT = new JLabel("UnSatisfiables: ");
		JTextField idUNSAT = new JTextField(Integer.toString(listStrUnSatisfiables.size())); 
		idUNSAT.setPreferredSize(d);
		idUNSAT.setEditable(false);
		idUNSAT.setHorizontalAlignment(JTextField.RIGHT);

		JLabel idLabelTimeElapsed = new JLabel("Time elapsed: ");
		long time = timeElapsed.toMillis();

		String strTime = time +" milliseconds";

		JTextField idTimeElapsed = new JTextField(strTime); 
		d = new Dimension();
		d.height=20;
		d.width=150;
		idTimeElapsed.setPreferredSize(d);
		idTimeElapsed.setEditable(false);
		idTimeElapsed.setHorizontalAlignment(JTextField.RIGHT);

		p1.add(idLabelNC);
		p1.add(idNC);

		p1.add(idLabelSAT);
		p1.add(idSAT);

		p1.add(idLabelUNSAT);
		p1.add(idUNSAT);

		p1.add(idLabelTimeElapsed);
		p1.add(idTimeElapsed);

		return p1;
	}
	private JPanel makeBottom() {
		p3 = new JPanel();
		p3.setLayout(new FlowLayout(FlowLayout.CENTER));

		closeButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				frame.dispose();// provis
			}
		});

		genGraphButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				creaGrafo(strCmbSel,false,false);
			}
		});
		genGraphButtonD.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				creaGrafo(strCmbSel,false,true);
			}
		});
		genGraphZoomButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				creaGrafo(strCmbSel,true,false);
			}
		});
		genGraphZoomButtonD.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				creaGrafo(strCmbSel,true,true);
			}
		});

		p3.add(closeButton);
		p3.add(genGraphButton);
		p3.add(genGraphButtonD);
		p3.add(genGraphZoomButton);
		p3.add(genGraphZoomButtonD);
		return p3;
	}

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

	private void creaGrafo(String combinacion, boolean bZoom, boolean showDes) {
		if (combinacion.equals("")) {
			return;
		}
		//		 1 -> 2 [penwidth=1, arrowhead=none, color=blue]
		//		 1 -> 3 [penwidth=1, arrowhead=none, color=blue]
		//		 2 -> 3 [penwidth=1, arrowhead=none, color=blue]


		// Anyadimos las invariantes que no estan 
		String[] partes = combinacion.split("-");		
		int numPartes=partes.length;

		String cfgNodosNO = "node [shape=ellipse fillcolor=\"orange\" style=\"filled\"]";
		String cfgNodosSI = "node [shape=ellipse fillcolor=\"lawngreen\" style=\"filled\"]";
		String strRes = "";
		boolean pVez = true;
		int nInv=0;
		for (IInvariant invSAT: listInvSatisfiables) {
			nInv+=1;
			String desInv = invSAT.name();
			String codCmb = String.valueOf(nInv);
			String strNinv = String.format("%0"+String.valueOf(listInvSatisfiables.size()).length()+"d",nInv);
			boolean esta = false;
			for (int nParte = 0 ; nParte < numPartes ; nParte++) {
				String parte = partes[nParte];
//				if (codCmb.equals(parte)) {
					if (strNinv.equals(parte)) {
					esta=true;
				}
			}
			if (!esta) {
				if (pVez) {
					strRes+= cfgNodosNO + "\r\n";
					pVez=false;
				}
				if (showDes) {
					strRes+= desInv + "\r\n";
				}else{
//					strRes+= codCmb + "\r\n";
					strRes+= strNinv + "\r\n";
				}
			}
		}

		strRes+= cfgNodosSI + "\r\n";
		String strCmb = "";
		strCmb = desarrollaCmb(combinacion, strRes, showDes);

		creaFileGrafo(strCmb, combinacion, bZoom);

	}

	private void creaFileGrafo(String strCmb, String combinacion, boolean bZoom) {

		String strFileIn = strRuta + "\\" + strNomFileIn;
		String strFileOut = strRuta + "\\" + strNomFileOut;
		StringBuffer sb = new StringBuffer();
		sb.append ("digraph R {\r\n");
		sb.append ("label = \"Combination " +combinacion + "\"\r\n");

		sb.append (strCmb);
		sb.append ("\r\n}");

		// Graba fichero en directorio temporal
		BufferedWriter writer = null;
		try {
			File file = new File(strFileIn);
			writer = new BufferedWriter(new FileWriter(file));
			writer.write(sb.toString());
		} catch (Exception e) {
			e.printStackTrace();
		} finally {
			if (writer != null)
				try {
					writer.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
		}

		// Ejecuta dot para Graphiz
		String cmd = "dot -Kdot -Tpng	 " + strFileIn + " -o " + strFileOut;
		boolean isWindows = System.getProperty("os.name")
				.toLowerCase().startsWith("windows");

		if (isWindows) {
			try {
				Process process;
				process = Runtime.getRuntime()
						.exec(String.format("cmd.exe /c "+cmd));

				// Espera a que acabe la generacion del grafico
				try {
					process.waitFor();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				img = new ImageIcon();
				img1 = new ImageIcon(strFileOut).getImage().getScaledInstance(wSizeImg, hSizeImg,Image.SCALE_DEFAULT);
				img.setImage(img1);

				lbImgGraph.setIcon(img);
				if (bZoom) {
					JDialog dialog = new JDialog();
					ImageIcon imgIcon2 = new ImageIcon();
					Image imgage2 = new ImageIcon(strFileOut).getImage().getScaledInstance(wSizeDlg, hSizeDlg,Image.SCALE_DEFAULT);
					imgIcon2.setImage(imgage2);
					JLabel label = new JLabel( imgIcon2 );
					dialog.add( label );

					dialog.pack();
					dialog.setLocationRelativeTo(parent);
					dialog.setVisible(true);
				}


			} catch (IOException e) {
				e.printStackTrace();
			}
		} else {
			// Adaptar para linux
		}
	}

	private String desarrollaCmb(String combinacion, String strAcum, boolean showDes) {
		String strCfg = "[penwidth=1, arrowsize=0.5, color=green, dir=both]";
		String strRes = strAcum;
		String[] partes = combinacion.split("-");		


		String parte1 = partes[0];
		String desInvParte1="";
		IInvariant invSAT = (IInvariant) mapInvSAT.get(Integer.parseInt(parte1));
		desInvParte1=invSAT.name();
		int numPartes=partes.length;
		if (numPartes == 1) {
			if (showDes) {
				strRes = desInvParte1 + " " + strCfg;
			}else{
				strRes = parte1 + " " + strCfg;
			}

			return strRes;
		}
		String desInv="";
		for (int i = 1 ; i < numPartes ; i++) {
			String strCmb="";
			String otraParte = partes[i].trim();

			if (showDes) {
				invSAT = (IInvariant) mapInvSAT.get(Integer.parseInt(otraParte));
				desInv=invSAT.name();
				strCmb = desInvParte1 + " -> " + desInv;
			}else{
				strCmb = parte1 + " -> " + otraParte;
			}
			strCmb+=" "+strCfg;
			if (strRes !="") {
				strRes += "\r\n";
			}
			strRes+=strCmb;
		}
		if (numPartes > 2) {
			String newCmb = "";
			for (int i = 1 ; i < numPartes ; i++) {
				String otraParte = partes[i].trim();
				if (newCmb !="") {
					newCmb += "-";
				}
				newCmb+=otraParte;
			}
			strRes = desarrollaCmb(newCmb, strRes,showDes);
		}
		return strRes;
	}
	private JPanel make1(Collection<IInvariant> listInv, boolean showNumber) {

		JPanel p2 = new JPanel();
		p2.setLayout(new FlowLayout(FlowLayout.LEFT));
		Dimension d = new Dimension();
		int heightBase = listInv.size()*25;
		d.height=heightBase;
		p2.setPreferredSize(d);

		DefaultListModel<String> listModel = new DefaultListModel<>();
		int nInv=0;
		for (IInvariant invSAT: listInv) {
			nInv+=1;
			if (showNumber) {
				listModel.addElement(nInv + " - " + invSAT.name());
			}else {
				listModel.addElement(invSAT.name());
			}
		}

		JList<String> lInv = new JList<String>(listModel);

		d = new Dimension();
		d.height=170;
		d.width=250;
		lInv.setPreferredSize(d);

		final JTextArea textArea= new JTextArea();

		lInv.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {

				String valor = lInv.getSelectedValue().trim();
				//				String descInvs = getValueListCombi(valor);
				String descInvs = getValueList1(valor,showNumber);
				textArea.setText(descInvs);
				int heightBaseInvs = descInvs.length()-descInvs.replace("\n","").length();
				Dimension d = new Dimension();
				d.height=heightBaseInvs*25;
				d.width=600;
				textArea.setPreferredSize(d);
				if (evt.getClickCount() == 2 && evt.getButton() == MouseEvent.BUTTON1) {

				}
			}
		});

		String descInvs="";

		if (listModel.size()>0) {
			lInv.setSelectedIndex(0);
			String valor = listModel.get(0).trim();
			descInvs = getValueList1(valor,showNumber);
		}

		textArea.setText(descInvs);

		JScrollPane scroll = new JScrollPane (lInv); 
		scroll.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		d = new Dimension();
		d.height=170;
		d.width=250;
		scroll.setPreferredSize(d);

		d = new Dimension();
		d.height=170;
		d.width=600;

		textArea.setLineWrap(true);
		JScrollPane scrollPane = new JScrollPane(textArea); 
		scrollPane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		scrollPane.setPreferredSize(d);
		textArea.setEditable(false);

		p2.add(scroll);
		p2.add(scrollPane);

		return p2;
	}

	private JPanel makeCombi(List<String> listStr, String nomTab) {

		JPanel p2 = new JPanel();
		p2.setLayout(new FlowLayout(FlowLayout.LEFT));
		Dimension d = new Dimension();
		int heightBase = listStr.size()*17;
		d.height=heightBase;
		p2.setPreferredSize(d);

		DefaultListModel<String> listModel = new DefaultListModel<>();
		int nInv=0;
		for (String strSAT: listStr) {
			nInv+=1;
			listModel.addElement(String.format("%5s",nInv )+ " : " + strSAT);
		}

		JList<String> lCombis = new JList<String>(listModel);

		if (listModel.size()>0) {
			lCombis.setSelectedIndex(0);
			String valor = lCombis.getSelectedValue().trim();
			if (tabbedPane.getSelectedIndex()==2) {
				String[] partes = valor.split(":");
				strCmbSel = partes[1].trim();
			}
		}

		d = new Dimension();
		d.height=heightBase;
		d.width=250;
		lCombis.setPreferredSize(d);
		lCombis.addListSelectionListener(new ListSelectionListener() {

			@Override
			public void valueChanged(ListSelectionEvent e) {
				if (tabbedPane.getSelectedIndex()==2) {
					String valor = lCombis.getSelectedValue().trim();
					String[] partes = valor.split(":");
					strCmbSel = partes[1].trim();
				}
			}
		});

		final JTextArea textArea= new JTextArea();

		lCombis.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {

				String valor = lCombis.getSelectedValue().trim();
				String[] partes = valor.split(":");
				String combinacion = partes[1].trim();
				if (tabbedPane.getSelectedIndex()==2) {
					strCmbSel=combinacion;
				}
				String descInvs = getValueListCombi(valor);
				textArea.setText(descInvs);
				int heightBaseInvs = descInvs.length()-descInvs.replace("\n","").length();
				Dimension d = new Dimension();
				d.height=heightBaseInvs*17;
				d.width=600;
				textArea.setPreferredSize(d);
				if (evt.getClickCount() == 2 && evt.getButton() == MouseEvent.BUTTON1) {

					Solution solution=null;
					KodkodSolver kodkodSolver = new KodkodSolver();
					try {
						solution = kodParent.calcular( combinacion,  invClassTotal);
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

		String descInvs="";

		if (listModel.size()>0) {
			lCombis.setSelectedIndex(0);
			String valor = lCombis.getSelectedValue().trim();
			if (nomTab.equals("SAT")) {
				String[] partes = valor.split(":");
				strCmbSel = partes[1].trim();
			}
		}

		textArea.setText(descInvs);

		JScrollPane scroll = new JScrollPane (lCombis); 
		scroll.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);

		d = new Dimension();
		d.height=170;
		d.width=250;
		scroll.setPreferredSize(d);

		d = new Dimension();
		int heightBaseInvs = descInvs.length()-descInvs.replace("\n","").length();
		d.height=heightBaseInvs*17;
		d.width=400;
		textArea.setPreferredSize(d);

		textArea.setLineWrap(true);
		textArea.setAutoscrolls(true);
		JScrollPane scrollPane = new JScrollPane(textArea); 
		scrollPane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		d = new Dimension();
		d.height=170;
		d.width=400;
		scrollPane.setPreferredSize(d);
		textArea.setEditable(false);

		p2.add(scroll);
		p2.add(scrollPane);	
		if (nomTab.equals("SAT")) {

			img = new ImageIcon();
			lbImgGraph = new JLabel(img);

			JPanel scrollImg = new JPanel(); 
			d = new Dimension();
			d.height=170;
			d.width=200;
			scrollImg.add(lbImgGraph);
			scrollImg.setPreferredSize(d);
			p2.add(scrollImg);
		}else {

		}

		return p2;
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

	private String getValueList1(String valor,boolean showNumber) {

		String[] partes = valor.split("-");
		String nameInv = "";
		int numElem=0;
		if (showNumber) {
			numElem=1;
		}
		nameInv = ((String) partes[numElem]).trim();
		String descInvs="";

		for (MClassInvariant minvSAT: mModel.classInvariants()) {
			if (minvSAT.name().equals(nameInv)) {
				descInvs=minvSAT.cls().name()+"::"+nameInv;
				descInvs+="\n   "+minvSAT.bodyExpression().toString();
			}
		}
		return descInvs;
	}

	private String getValueListCombi(String valor) {

		String[] partesIni = valor.split(":");
		String[] partes = partesIni[1].split("-");
		String descInvs="";
		for (int i = 0 ; i < partes.length ; i++) {
			String descParte = partes[i].trim();
			String nomClass="";
			String nomInv="";
			// Busca invariantes de la combinacion en lista de satisfiables

			int order = Integer.parseInt(descParte); 
			if (mapInvSAT.containsKey(order)) {
				IInvariant inv = (IInvariant) mapInvSAT.get(order);
				nomClass=inv.clazz().name();
				nomInv = inv.name();	
				if (descInvs != "") {
					descInvs +="\n";
				}
				descInvs+=nomClass + "::" + nomInv;
			}
		}
		return descInvs;
	}
	private JPanel makeRanking() {

		JPanel p2 = new JPanel();
		Map<Integer, Integer> mapRnk = new HashMap<>();

		for (String strSAT: listStrSatisfiables) {
			String[] partes = strSAT.split("-");
			int numPartes=partes.length;
			if (mapRnk.containsKey(numPartes)) {
				int valor = mapRnk.get(numPartes)+1;
				mapRnk.remove(numPartes);
				mapRnk.put(numPartes, valor);
			}else {
				mapRnk.put(numPartes,1);
			}
		}

		Map<Integer, Integer> reverseSortedMap = new TreeMap<Integer, Integer>(Collections.reverseOrder());
		reverseSortedMap.putAll(mapRnk);

		Dimension d = new Dimension();
		int heightBase = mapRnk.size()*17;
		d.height=heightBase;
		p2.setPreferredSize(d);


		DefaultListModel<String> listModel = new DefaultListModel<>();
		listModel.addElement("           Num. Invs. Total combinaciones");
		listModel.addElement("           ====================================================================");

		for (Map.Entry<Integer, Integer> entry : reverseSortedMap.entrySet()) {
			int intKey = entry.getKey();
			int intValor = entry.getValue();
			String strRanking = String.format("%20s",intKey) + "  " + String.format("%s",intValor);
			listModel.addElement(strRanking);
		}

		JList<String> lInv = new JList<String>(listModel);
		d = new Dimension();
		d = new Dimension();
		d.height=listModel.size()*17;
		d.width=600;
		lInv.setPreferredSize(d);
		Font font = new Font("Courier New", Font.BOLD, 12);
		lInv.setFont(font);

		JScrollPane scroll = new JScrollPane (lInv); 
		scroll.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		d = new Dimension();
		d.height=170;
		d.width=600;
		scroll.setPreferredSize(d);		

		String strRanking="";
		strRanking += String.format("%20s","Num.Inv") + " " + String.format("%20s","Total combinaciones");
		strRanking += "\n" + String.format("%20s","=======") + " " + String.format("%20s","===================");
		for (Map.Entry<Integer, Integer> entry : reverseSortedMap.entrySet()) {
			if (strRanking != "") {
				strRanking +="\n";
			}
			strRanking += String.format("%20s",entry.getKey()) + " " + String.format("%20s",entry.getValue());
		}

		p2.add(scroll);
		return p2;
	}
	private JPanel makeRankingGrupos(HashMap<String, String> map) {

		JPanel p2 = new JPanel();

		Map<String, String> mapRnk = new HashMap<>();

		for (Map.Entry<String, String> entry : map.entrySet()) {
			String key = entry.getKey();
			String value = entry.getValue();
			int intValor=Integer.parseInt(value);
			String[] partes = key.split("-");
			int nPartes = partes.length;
			if (intValor > 1) {
				String strValorfmt = String.format("%5s", nPartes).replace(' ', '0')+"-"+String.format("%5s", value).replace(' ', '0');
				String strValor=strValorfmt + " " + key;
				mapRnk.put(strValor,key);			
			}
		}

		Dimension d = new Dimension();
		int heightBase = mapRnk.size()*17;
		d.height=heightBase;
		p2.setPreferredSize(d);

		Map<String, String> reverseSortedMap = new TreeMap<String, String>(Collections.reverseOrder());
		reverseSortedMap.putAll(mapRnk);

		DefaultListModel<String> listModel = new DefaultListModel<>();
		listModel.addElement("         nInvs Ocu    Invariants");
		listModel.addElement("         ====================================================================");
		for (Map.Entry<String, String> entry : reverseSortedMap.entrySet()) {
			String strValor = entry.getKey();
			String strOcu = strValor.substring(0, strValor.indexOf(" "));
			String strRanking = String.format("%20s",strOcu) + "  " + String.format("%s",entry.getValue());
			listModel.addElement(strRanking);
		}

		JList<String> lInv = new JList<String>(listModel);
		d = new Dimension();
		d = new Dimension();
		d.height=listModel.size()*17;
		d.width=600;
		lInv.setPreferredSize(d);
		Font font = new Font("Courier New", Font.BOLD, 12);
		lInv.setFont(font);

		JScrollPane scroll = new JScrollPane (lInv); 
		scroll.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
		d = new Dimension();
		d.height=170;
		d.width=600;
		scroll.setPreferredSize(d);		

		p2.add(scroll);
		return p2;
	}
}
