package org.tzi.mvm;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.tzi.kodkod.KodkodModelValidator;
import org.tzi.kodkod.ResInv;
import org.tzi.kodkod.model.iface.IInvariant;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.uml.mm.MModel;

public class ParamDialogValidator {

	private MainWindow parent=null;
	private KodkodModelValidator kodParent=null;
	private Collection<IInvariant> listInvSatisfiables = null;
	private Collection<IInvariant> listInvUnSatisfiables = null;
	private List<String> listStrSatisfiables = null;
	private List<String> listStrUnSatisfiables = null;
	private HashMap<String, ResInv> mapInvRes=null;
	private MModel mModel;
	private Collection<IInvariant> invClassTotal=null;
	private Duration timeElapsed;
	private int numCallSolver;
	private int numCallSolverSAT;
	private int numCallSolverUNSAT;
	private String pTipoSearchMSS;	
	private int numberIter=1;

	public ParamDialogValidator(final MainWindow parent, 
			KodkodModelValidator kodParent,
			Collection<IInvariant> pListInvSatisfiables, 
			Collection<IInvariant> pListInvUnSatisfiables,
			Collection<IInvariant> pListInvOthers,
			List<String> pListStrSatisfiables,
			List<String> pListStrUnSatisfiables,
			HashMap<String, ResInv> pMapInvRes,
			MModel pMModel,
			Collection<IInvariant> pInvClassTotal ,
			Duration pTimeElapsed,
			int pNumCallSolver,
			int pNumCallSolverSAT,
			int pNumCallSolverUNSAT,
			String tipoSearchMSS,
			int pNumberIter) {

		this.parent=parent;
		this.kodParent=kodParent;
		this.listInvSatisfiables = pListInvSatisfiables;
		this.listInvUnSatisfiables = pListInvUnSatisfiables;
		this.listStrSatisfiables = sortBynNumInvs(pListStrSatisfiables,true);
		this.listStrUnSatisfiables = sortBynNumInvs(pListStrUnSatisfiables,false);
		this.mapInvRes = pMapInvRes;	
		this.mModel=pMModel;
		this.invClassTotal = pInvClassTotal;
		this.timeElapsed=pTimeElapsed;
		this.numCallSolver = pNumCallSolver;
		this.numCallSolverSAT = pNumCallSolverSAT;
		this.numCallSolverUNSAT = pNumCallSolverUNSAT;
		this.pTipoSearchMSS=tipoSearchMSS;
		numberIter=pNumberIter;
	}

	public ParamDialogValidator() {

	}

	public MainWindow getParent() {
		return parent;
	}

	public void setParent(MainWindow parent) {
		this.parent = parent;
	}

	public KodkodModelValidator getKodParent() {
		return kodParent;
	}

	public void setKodParent(KodkodModelValidator kodParent) {
		this.kodParent = kodParent;
	}

	public Collection<IInvariant> getListInvSatisfiables() {
		return listInvSatisfiables;
	}

	public void setListInvSatisfiables(Collection<IInvariant> listInvSatisfiables) {
		this.listInvSatisfiables = listInvSatisfiables;
	}

	public Collection<IInvariant> getListInvUnSatisfiables() {
		return listInvUnSatisfiables;
	}

	public void setListInvUnSatisfiables(Collection<IInvariant> listInvUnSatisfiables) {
		this.listInvUnSatisfiables = listInvUnSatisfiables;
	}

	public List<String> getListStrSatisfiables() {
		return listStrSatisfiables;
	}

	public void setListStrSatisfiables(List<String> listStrSatisfiables) {
		this.listStrSatisfiables = listStrSatisfiables;
	}

	public List<String> getListStrUnSatisfiables() {
		return listStrUnSatisfiables;
	}

	public void setListStrUnSatisfiables(List<String> listStrUnSatisfiables) {
		this.listStrUnSatisfiables = listStrUnSatisfiables;
	}

	public HashMap<String, ResInv> getMapInvRes() {
		return mapInvRes;
	}

	public void setMapInvRes(HashMap<String, ResInv> mapInvRes) {
		this.mapInvRes = mapInvRes;
	}

	public MModel getmModel() {
		return mModel;
	}

	public void setmModel(MModel mModel) {
		this.mModel = mModel;
	}

	public Collection<IInvariant> getInvClassTotal() {
		return invClassTotal;
	}

	public void setInvClassTotal(Collection<IInvariant> invClassTotal) {
		this.invClassTotal = invClassTotal;
	}

	public Duration getTimeElapsed() {
		return timeElapsed;
	}

	public void setTimeElapsed(Duration timeElapsed) {
		this.timeElapsed = timeElapsed;
	}

	public int getNumCallSolver() {
		return numCallSolver;
	}

	public void setNumCallSolver(int numCallSolver) {
		this.numCallSolver = numCallSolver;
	}

	public int getNumCallSolverSAT() {
		return numCallSolverSAT;
	}

	public void setNumCallSolverSAT(int numCallSolverSAT) {
		this.numCallSolverSAT = numCallSolverSAT;
	}

	public int getNumCallSolverUNSAT() {
		return numCallSolverUNSAT;
	}

	public void setNumCallSolverUNSAT(int numCallSolverUNSAT) {
		this.numCallSolverUNSAT = numCallSolverUNSAT;
	}

	public String getpTipoSearchMSS() {
		return pTipoSearchMSS;
	}

	public void setpTipoSearchMSS(String pTipoSearchMSS) {
		this.pTipoSearchMSS = pTipoSearchMSS;
	}

	public int getNumberIter() {
		return numberIter;
	}

	public void setNumberIter(int numberIter) {
		this.numberIter = numberIter;
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



}


