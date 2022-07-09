package org.tzi.use.kodkod.plugin.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Image;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;
import java.time.Duration;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import javax.imageio.ImageIO;
import javax.swing.DefaultListModel;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;

import org.tzi.kodkod.model.iface.IInvariant;
import org.tzi.use.uml.mm.MClassInvariant;
import org.tzi.use.uml.mm.MModel;

public class ValidatorJuantoDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JFrame frame;  

	Collection<IInvariant> listInvSatisfiables = null;
	Collection<IInvariant> listInvUnSatisfiables = null;
	Collection<IInvariant> listInvOthers = null;
	List<String> listStrSatisfiables = null;
	List<String> listStrUnSatisfiables = null;
	List<String> listStrOthers = null;

	Map<Integer, IInvariant> mapInvSAT;

	MModel mModel;
	Duration timeElapsed;
	
	public ValidatorJuantoDialog(final JFrame parent, 
			Collection<IInvariant> listInvSatisfiables, 
			Collection<IInvariant> listInvUnSatisfiables,
			Collection<IInvariant> listInvOthers,
			List<String> listStrSatisfiables,
			List<String> listStrUnSatisfiables,
			List<String> listStrOthers,
			MModel mModel,
			Duration timeElapsed) {

		this.listInvSatisfiables = listInvSatisfiables;
		this.listInvUnSatisfiables = listInvUnSatisfiables;
		this.listInvOthers = listInvOthers;
		this.listStrSatisfiables = listStrSatisfiables;
		this.listStrUnSatisfiables = listStrUnSatisfiables;
		this.listStrOthers = listStrOthers;
		this.timeElapsed = timeElapsed;
		
//		ImageIcon icon = new ImageIcon("resources/MvMJG.png",
//                "MvM");
//		Image img = (new ImageIcon(icon)).getImage();
//		setIconImage(icon);
		
//		Image im = Toolkit.getDefaultToolkit().getImage("C:\\Users\\Juanto\\git\\JuantoModelValidator\\ModelValidatorPlugin\\resources\\MvMJG.png");
//		try {
//			Image img = ImageIO.read(getClass().getResource("C:\\Users\\Juanto\\git\\JuantoModelValidator\\ModelValidatorPlugin\\resources\\\\MvMJG.png"));
//			this.setIconImage(img);
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		
//		Image icon = Toolkit.getDefaultToolkit().getImage("C:\\Users\\Juanto\\git\\JuantoModelValidator\\ModelValidatorPlugin\\resources\\MvMJG.png");    
////		f.setIconImage(icon); 
////		this.frame.setIconImage(icon);
//		
//		setIconImage(icon);
		


		mapInvSAT = new HashMap<>();
		int i = 0;
		for (IInvariant invClass: listInvSatisfiables) {
			i+=1;
			mapInvSAT.put(i, invClass);
		}

		this.mModel=mModel;
		frame = new JFrame("Validator con combinaciones");
		
//		Image icono = Toolkit.getDefaultToolkit().getImage("C:\\Users\\Juanto\\git\\JuantoModelValidator\\ModelValidatorPlugin\\resources\\MvMJG.png");  
		Image icono = Toolkit.getDefaultToolkit().getImage("resources/MvMJG.png");
		frame.setIconImage(icono); 

		
		frame.setSize(820, 280);
		frame.setVisible(true);
		frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE); 
		frame.getContentPane().setLayout(new BorderLayout());

		JPanel p = new JPanel();
		p.setLayout(new BorderLayout());

		p.add(makeComun(listStrSatisfiables.size() , listStrUnSatisfiables.size(), timeElapsed),BorderLayout.NORTH);

		JTabbedPane  tabbedPane = new JTabbedPane(JTabbedPane.TOP);
		pack();

		tabbedPane.addTab("Satisfiables uni", make1(listInvSatisfiables,true));
		tabbedPane.addTab("UnSatisfiables uni.", make1(listInvUnSatisfiables,false));
		tabbedPane.addTab("Satisfiables comb.", makeCombi(listStrSatisfiables));
		tabbedPane.addTab("UnSatisfiables comb.", makeCombi(listStrUnSatisfiables));
		tabbedPane.addTab("Others comb.", makeCombi(listStrOthers));
		tabbedPane.addTab("Ranking Comb. Satisf.", makeRanking());

		p.add(tabbedPane,BorderLayout.CENTER);

		p.add(makeBottom(), BorderLayout.SOUTH);

		frame.getContentPane().add(p);
		frame.setMinimumSize(new Dimension(getWidth(), getHeight()));
		frame.setLocationRelativeTo(this);
		frame.setEnabled(true);
	}
	private JPanel makeComun(int nSAT, int nUNSAT, Duration timeElapsed) {
		JPanel p1 = new JPanel();
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
		JTextField idTimeElapsed = new JTextField(timeElapsed.toMillis() +" milliseconds"); 
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
		JPanel p3 = new JPanel();
		p3.setLayout(new FlowLayout(FlowLayout.CENTER));

		JButton closeButton = new JButton("Close");
		closeButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
				frame.dispose();
			}
		});

		p3.add(closeButton);
		return p3;
	}

	private JPanel make1(Collection<IInvariant> listInv, boolean showNumber) {

		JPanel p2 = new JPanel();
		p2.setLayout(new FlowLayout(FlowLayout.LEFT));
		Dimension d = new Dimension();
		int heightBase = listInv.size()*17;
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
		d.height=120;
		d.width=180;
		lInv.setPreferredSize(d);

		final JTextArea textArea= new JTextArea();

		lInv.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {
				String valor = lInv.getSelectedValue();
				String descInvs = getValueList1(valor,showNumber);
				textArea.setText(descInvs);
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
		d = new Dimension();
		d.height=120;
		d.width=180;
		scroll.setPreferredSize(d);


		d = new Dimension();
		d.height=136;
		d.width=600;
		textArea.setPreferredSize(d);

		textArea.setLineWrap(true);
		JScrollPane scrollPane = new JScrollPane(textArea); 
		textArea.setEditable(false);

		p2.add(scroll);
		p2.add(scrollPane);

		return p2;
	}


	private JPanel makeCombi(List<String> listStr) {

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
			listModel.addElement(String.format("%10s",nInv )+ " : " + strSAT);
		}

		JList<String> lCombis = new JList<String>(listModel);

		d = new Dimension();
		d.height=heightBase;
		d.width=170;
		lCombis.setPreferredSize(d);

		final JTextArea textArea= new JTextArea();

		lCombis.addMouseListener(new MouseAdapter() {
			public void mouseClicked(MouseEvent evt) {
				String valor = lCombis.getSelectedValue().trim();
				String descInvs = getValueListCombi(valor);
				textArea.setText(descInvs);
			}
		});

		String descInvs="";

		if (listModel.size()>0) {
			lCombis.setSelectedIndex(0);
			String valor = listModel.get(0).trim();
			descInvs = getValueListCombi(valor);
		}

		textArea.setText(descInvs);

		JScrollPane scroll = new JScrollPane (lCombis); 
		scroll.setAutoscrolls(true);
		d = new Dimension();
		d.height=136;
		d.width=170;
		scroll.setPreferredSize(d);

		d = new Dimension();
		d.height=136;
		d.width=600;
		textArea.setPreferredSize(d);

		textArea.setLineWrap(true);
		JScrollPane scrollPane = new JScrollPane(textArea); 
		textArea.setEditable(false);

		p2.add(scroll);
		p2.add(scrollPane);

		return p2;
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

		String strRanking="";
		strRanking += String.format("%20s","Num.Inv") + " " + String.format("%20s","Total combinaciones");
		strRanking += "\n" + String.format("%20s","=======") + " " + String.format("%20s","===================");
		for (Map.Entry<Integer, Integer> entry : reverseSortedMap.entrySet()) {
			if (strRanking != "") {
				strRanking +="\n";
			}
			strRanking += String.format("%20s",entry.getKey()) + " " + String.format("%20s",entry.getValue());
		}

		final JTextArea textArea= new JTextArea();
		textArea.setText(strRanking);

		Dimension d = new Dimension();
		d.height=136;
		d.width=600;
		textArea.setPreferredSize(d);

		textArea.setLineWrap(true);
		JScrollPane scrollPane = new JScrollPane(textArea); 
		textArea.setEditable(false);

		p2.add(scrollPane);
		return p2;
	}
}
