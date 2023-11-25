package org.tzi.mvm;
import java.awt.Color;
import java.awt.Dialog.ModalExclusionType;
import java.awt.Dialog.ModalityType;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
//import java.awt.event.KeyListener;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javax.swing.AbstractButton;
import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.border.Border;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.JTableHeader;

import org.tzi.mvm.AssocWizard;
import org.tzi.mvm.LinkWizard;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.gui.views.WizardMVMView;

public class MVMWizardAssoc extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	private JFrame frame;
	private JPanel panel;
	private JPanel pProposals;
	private JScrollPane pScrollProposals ;

	private DefaultTableModel modelTabAssocs;
	private DefaultTableModel modelTabLinks;

	private JTableHeader header;

	private JLabel lbAssociations;
	private JLabel lbLinks;

	private JLabel lbCause;	
	private JLabel lbFullMessage;	

	private JTextField txCause;
	private JTextArea txFullMessage;
	private JScrollPane scrollBarFullMessage;

	private JTable tabAssocs;
	private JScrollPane paneTabAssocs;

	private JTable tabLinks;
	private JScrollPane paneTabLinks;

	private JButton btnApply;
	private JButton btnExit;

	private ButtonGroup group;

	private ArrayList<AssocWizard> lAssocs;

	private AssocWizard assocPral;
	private String commandWizard;

	private List<AssocWizard> lAssocsWizard;

	private Border etchedTitledBorder;
	private Border etchedBorder;

	private int HEIGHT_TABLE = 100;

	public MVMWizardAssoc(JFrame fParent, List<AssocWizard> lAssocsParent) {
		super(fParent, "Wizard Association",ModalityType.APPLICATION_MODAL);

		lAssocsWizard = lAssocsParent;
		commandWizard="";
		frame = new JFrame("Wizard Association");
		frame.setAlwaysOnTop(true);
		frame.setModalExclusionType(ModalExclusionType.TOOLKIT_EXCLUDE);
		frame.setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
		frame.setLocationRelativeTo(null);

		modelTabAssocs = new DefaultTableModel();
		tabAssocs = new JTable(modelTabAssocs);

		modelTabLinks = new DefaultTableModel();
		tabLinks = new JTable(modelTabLinks);

		panel = new JPanel();
		frame.add(panel);

		panel.setLayout(null);

		lbAssociations = new JLabel("Associations");
		lbAssociations.setBounds(15, 15, 100, 25);
		panel.add(lbAssociations);	

		lbLinks = new JLabel("Links");
		lbLinks.setBounds(230, 15, 100, 25);
		panel.add(lbLinks);	

		tabAssocs = new JTable(modelTabAssocs);
		tabAssocs.setBounds(15, 40, 210, HEIGHT_TABLE);
		tabAssocs.setDefaultEditor(Object.class, null);// Para no poder editar

		header = tabAssocs.getTableHeader();
		header.setBackground(Color.lightGray);
		header.setVisible(true);

		tabAssocs.addMouseListener(new java.awt.event.MouseAdapter() {
			@Override
			public void mouseClicked(java.awt.event.MouseEvent evt) {
				int row = tabAssocs.rowAtPoint(evt.getPoint());
				showInfoAssocFromRow(row);
			}
		});

		tabAssocs.addKeyListener(new KeyAdapter() {
			@Override
			public void keyPressed(KeyEvent e) {
				if (e.getKeyCode() == KeyEvent.VK_DOWN || e.getKeyCode() == KeyEvent.VK_UP ){
					int row = tabAssocs.getSelectedRow();
					showInfoAssocFromRow(row);
				}
			}
			@Override
			public void keyReleased(KeyEvent e) {
				if (e.getKeyCode() == KeyEvent.VK_DOWN || e.getKeyCode() == KeyEvent.VK_UP ){
					int row = tabAssocs.getSelectedRow();
					showInfoAssocFromRow(row);
				}
			}
		});

		paneTabAssocs = new JScrollPane(tabAssocs);
		paneTabAssocs.setBounds(15, 40, 210, HEIGHT_TABLE);
		panel.add(paneTabAssocs);

		loadTableAssocs();
		adjustWidthColumnsAssocs();

		tabLinks = new JTable(modelTabLinks);
		tabLinks.setBounds(230, 40, 655, HEIGHT_TABLE);
		tabLinks.setDefaultEditor(Object.class, null);// Para no poder editar

		header = tabLinks.getTableHeader();
		header.setBackground(Color.lightGray);
		header.setVisible(true);

		tabLinks.addMouseListener(new java.awt.event.MouseAdapter() {
			@Override
			public void mouseClicked(java.awt.event.MouseEvent evt) {
				int row = tabLinks.rowAtPoint(evt.getPoint());
				showInfoLinkFromRow(row);
			}
		});

		tabLinks.addKeyListener(new KeyAdapter() {
			@Override
			public void keyPressed(KeyEvent e) {
				if (e.getKeyCode() == KeyEvent.VK_DOWN || e.getKeyCode() == KeyEvent.VK_UP ){

					int row = tabLinks.getSelectedRow();
					showInfoLinkFromRow(row);
				}
			}
			@Override
			public void keyReleased(KeyEvent e) {
				if (e.getKeyCode() == KeyEvent.VK_DOWN || e.getKeyCode() == KeyEvent.VK_UP ){

					int row = tabLinks.getSelectedRow();
					showInfoLinkFromRow(row);
				}
			}
		});

		paneTabLinks = new JScrollPane(tabLinks);
		paneTabLinks.setBounds(230, 40, 655, HEIGHT_TABLE);
		panel.add(paneTabLinks);

		Object o = tabAssocs.getValueAt(0, 0);
		assocPral= new AssocWizard();

		if (!o.toString().equals("")) {
			// buscar assoc en lista			
			assocPral=findInfoAssoc(o.toString());
		}

		lbCause = new JLabel("Cause");
		lbCause.setBounds(15, 45+HEIGHT_TABLE, 100, 25);
		panel.add(lbCause);	

		txCause = new JTextField();
		txCause.setBounds(15, 70+HEIGHT_TABLE, 870, 25);
		Color color = Color.WHITE;
		txCause.setBackground(color);

		Border border = BorderFactory.createLineBorder(Color.GRAY, 1);
		txCause.setBorder(border);
		txCause.setEditable(false);

		panel.add(txCause);

		lbFullMessage = new JLabel("Full Message");
		lbFullMessage.setBounds(15, 100+HEIGHT_TABLE, 100, 25);
		panel.add(lbFullMessage);	

		txFullMessage = new JTextArea();
		txFullMessage.setEditable(false);
		txFullMessage.setLineWrap(true);

		scrollBarFullMessage = new JScrollPane(txFullMessage,
				JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
				JScrollPane.HORIZONTAL_SCROLLBAR_NEVER);
		scrollBarFullMessage.setBounds(15, 125+HEIGHT_TABLE, 870, 100);

		panel.add(scrollBarFullMessage);

		loadTableLinks(assocPral);
		assocPral = findInfoAssoc(assocPral.getName());
		tabAssocs.setRowSelectionInterval(0, 0);
		List<LinkWizard> lLinks = assocPral.getlLinks();
		LinkWizard oLink = findInfoLink(lLinks,0);
		showInfoLink( oLink);
		tabLinks.setRowSelectionInterval(0, 0);

		String borderTitle = "Proposals";
		etchedBorder = BorderFactory.createEtchedBorder();
		etchedTitledBorder = BorderFactory.createTitledBorder(etchedBorder, borderTitle);

		pScrollProposals = new JScrollPane(pProposals);
		pScrollProposals.setBounds(15, 235+HEIGHT_TABLE, 600, 100);
		pScrollProposals.setBorder(etchedTitledBorder);
		panel.add(pScrollProposals);

		showInfoAssocFromRow(0);
		showInfoLinkFromRow(0);

		btnApply = new JButton("Apply");
		btnApply.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent e) {
				//	ver que option esta seleccionada
				for (Enumeration<AbstractButton> buttons = group.getElements(); buttons.hasMoreElements();) {
					AbstractButton button = buttons.nextElement();

					if (button.isSelected()) {
						commandWizard=button.getActionCommand();
					}
				}
				dispose();

			}
		});
		btnApply.setBounds(630, 310+HEIGHT_TABLE, 120, 25);
		panel.add(btnApply);

		btnExit = new JButton("Salir");
		btnExit.addActionListener(new ActionListener() {

			@Override
			public void actionPerformed(ActionEvent e) {
				commandWizard="";
				dispose();
			}
		});
		btnExit.setBounds(760, 310+HEIGHT_TABLE, 120, 25);
		panel.add(btnExit);

		getContentPane().add(panel);
	}

	public String getCommandWizard() {
		return commandWizard;
	}
	private String[][] createActionLinks(Map<String, String> mapActions) {

		// [x][y]
		// [x]->Acciones
		// [y]->Comandos a devolver para su ejecucion
		String actionLinks[][] = new String[2][2];
		String strAction="";
		String textAction="";
		String strCommand="";
		for (Map.Entry<String, String> entry : mapActions.entrySet()) {

			String actionW =  entry.getKey();
			String infoW = entry.getValue();

			String pCar = actionW.substring(0,1);

			switch(pCar) {
			case "A":
				textAction = "Assign";
				if (strCommand!="") {
					strCommand+="|";
				}
				strCommand=strCommand+"A "+infoW;
				break;
			case "C":
				String sCar = actionW.substring(2,actionW.length());
				textAction = "Create ["+sCar+"] object/s";
				if (strCommand!="") {
					strCommand+="|";
				}
				strCommand=strCommand+"C "+sCar+" "+infoW;
				break;
			case "I":
				textAction = "Insert link";
				if (strCommand!="") {
					strCommand+="|";
				}
				strCommand=strCommand+"I "+infoW;
				break;			    
			default:

			}

			if (strAction!="") {
				strAction+=", ";
			}
			strAction+=textAction+":"+infoW;
		}

		actionLinks[0][0] = strAction;
		actionLinks[0][1] = strCommand;
		//strCommand
		actionLinks[1][0] = "Delete";
		actionLinks[1][1] = "D";
		return actionLinks;
	}
	private void showInfoAssocFromRow(int row) {
		String nomAssoc= tabAssocs.getValueAt(row, 0).toString();

		assocPral = findInfoAssoc(nomAssoc);
		loadTableLinks(assocPral);

		List<LinkWizard> lLinks = assocPral.getlLinks();
		LinkWizard oLink = findInfoLink(lLinks,0);
		tabLinks.setRowSelectionInterval(0, 0);

		showInfoLink( oLink);
	}

	private void showInfoLinkFromRow(int row) {
		List<LinkWizard> lLinks = assocPral.getlLinks();
		LinkWizard oLink = findInfoLink(lLinks,row);
		tabLinks.setRowSelectionInterval(row, row);

		showInfoLink( oLink);
		showPanelActionsLink(oLink);
	}
	private void showInfoLink(LinkWizard oLink) {
		txCause.setText(oLink.getCause());
		txFullMessage.setText(oLink.getFullMessage());
	}

	private void showPanelActionsLink(LinkWizard oLink) {
		Map<String, String> mapActions = new HashMap<String, String>();
		mapActions=oLink.getMapActions();
		String actionLinks[][] = createActionLinks(mapActions);

		pProposals = new JPanel();
		BoxLayout layout = new BoxLayout(pProposals, BoxLayout.Y_AXIS);
		pProposals.setLayout(layout);
		group = new ButtonGroup();
		boolean pVez = true;
		int sizeActions=actionLinks.length;
		for (int r=0;r<sizeActions;r++) {
			String strAction=actionLinks[r][0];
			String strCommand=actionLinks[r][1];
			JRadioButton rb = new JRadioButton (strAction);
			if (pVez) {
				rb.setSelected(true);
				rb.setActionCommand(strCommand);
				pVez=false;
			}
			pProposals.add(rb);
			group.add(rb);		
		}

		String borderTitle = "Proposals ("+ actionLinks.length+")";
		panel.remove(pScrollProposals);
		pScrollProposals = new JScrollPane(pProposals);
		pScrollProposals.setBounds(15, 235+HEIGHT_TABLE, 600, 100);
		etchedTitledBorder = BorderFactory.createTitledBorder(etchedBorder, borderTitle);
		pScrollProposals.setBorder(etchedTitledBorder);
		panel.add(pScrollProposals);
		panel.updateUI();

	}
	private LinkWizard findInfoLink(List<LinkWizard> lLinks,int row) {
		LinkWizard oLink = new LinkWizard();

		String nomObject = tabLinks.getValueAt(row, 0).toString();
		String nomRole = tabLinks.getValueAt(row, 4).toString();
		for(int i=0;i<lLinks.size();i++) {
			LinkWizard oLinkRef = lLinks.get(i);
			String nomObjectOref = oLinkRef.getObject().toString();
			String nomRoleOref = oLinkRef.getAssocEnd().toString();
			if (nomObjectOref.equals(nomObject) && nomRoleOref.equals(nomRole)) {
				return oLinkRef;
			}
		}

		return oLink;

	}
	private AssocWizard findInfoAssoc(String assocRef) {
		AssocWizard assoc = new AssocWizard();
		// find row of Assoc
		for (int i=0;i<lAssocs.size();i++) {
			assoc = lAssocs.get(i);
			if (assoc.getName().equals(assocRef)) {
				return assoc;
			}
		}
		return assoc;

	}
	private void loadTableAssocs() {
		modelTabAssocs = new DefaultTableModel();
		String[] columns;
		columns = new String[] {
				"Association", "State"
		};

		ArrayList<AssocWizard>data = loadAssocs();

		Object[][] objects = new Object[data.size()][2];
		for (int i=0;i<data.size();i++) {
			objects[i][0]= data.get(i).getName();
			objects[i][1]= data.get(i).getState();
		}

		modelTabAssocs = new DefaultTableModel(objects , columns);

		tabAssocs.setModel(modelTabAssocs);
		tabAssocs.repaint();
		return;
	}

	private ArrayList<AssocWizard> loadAssocs(){
		lAssocs = new ArrayList<AssocWizard>(lAssocsWizard);
		return lAssocs;		
	}

	private ArrayList<LinkWizard> loadLinksAssoc(AssocWizard assoc){
		ArrayList<LinkWizard> lLinks = new ArrayList<LinkWizard>(assoc.getlLinks());
		return lLinks;
	}
	private void loadTableLinks(AssocWizard assoc) {
		modelTabLinks = new DefaultTableModel();
		String[] columns;
		columns = new String[] {
				"Object", "Class","Connectec To","Of Class", "Assoc End","Multi Specified"
		};

		ArrayList<LinkWizard> data = loadLinksAssoc(assoc);

		Object[][] objects = new Object[data.size()][6];
		for (int i=0;i<data.size();i++) {
			objects[i][0]= data.get(i).getObject();
			objects[i][1]= data.get(i).getNomClass();
			objects[i][2]= data.get(i).getConnectedTo();
			objects[i][3]= data.get(i).getOfClass();
			objects[i][4]= data.get(i).getAssocEnd();
			objects[i][5]= data.get(i).getMultiSpecified();
		}


		modelTabLinks = new DefaultTableModel(objects,columns);
		tabLinks.setModel(modelTabLinks);
		adjustWidthColumnsLinks();
		tabLinks.repaint();
		return;
	}
	private void adjustWidthColumnsAssocs(){
		DefaultTableCellRenderer centerRenderer = new DefaultTableCellRenderer();
		centerRenderer.setHorizontalAlignment( JLabel.CENTER );
		tabAssocs.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
		tabAssocs.getColumnModel().getColumn(1).setCellRenderer( centerRenderer );
		tabAssocs.setAutoResizeMode(JTable.AUTO_RESIZE_NEXT_COLUMN);
	}
	private void adjustWidthColumnsLinks(){
		DefaultTableCellRenderer centerRenderer = new DefaultTableCellRenderer();
		centerRenderer.setHorizontalAlignment( JLabel.CENTER );
		tabLinks.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
		tabLinks.getColumnModel().getColumn(2).setCellRenderer( centerRenderer );
		tabLinks.getColumnModel().getColumn(5).setCellRenderer( centerRenderer );
		tabLinks.setAutoResizeMode(JTable.AUTO_RESIZE_NEXT_COLUMN);
	}
}
