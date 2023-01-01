package org.tzi.mvm;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class CollectionCmb extends HashMap<String,Combination>{
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	// Si la combinacion no esta incluida la incluye
	public boolean add(Combination e) {
		boolean suma=false;
		if (!this.containsKey(e.getKey())) {
			this.put(e.toString(), e);
			suma=true;
		}
		return suma;
	}

	// Se analiza si la coleccion contiene la combinacion de invariantes indicada	
	public boolean contiene(Combination e) {
		boolean contiene=this.containsKey(e.getKey());
		return contiene;
	}

	// Se analiza si alguna de las combinaciones de la coleccion contiene la combinacion indicada
	public boolean sameContains(Combination e) {
		boolean containedIn=false;
		for (Entry<String, Combination> item : this.entrySet()){
			Combination cmb = item.getValue();
			if (cmb.containsCmb(e)){
				containedIn=true;
				break;
			}
		}
		return containedIn;
	}

	// Se analiza si alguna de las combinaciones de la coleccion esta contenida en la combinacion indicada
	public boolean sameContainedIn(Combination e) {
		boolean containsSame=false;
		for (Entry<String, Combination> item : this.entrySet()){
			Combination cmb = item.getValue();
			if (cmb.cmbContainedIn(e)){
				containsSame=true;
				break;
			}
		}		
		return containsSame;
	}
	public List<Combination> getList(){
		List<Combination> lCmbs = new ArrayList<>(this.values());
		return lCmbs;
	}

	public void addAll(CollectionCmb colResSat) {
		for (Entry<String, Combination> item : colResSat.entrySet()){
			String key = item.getKey();
			Combination cmb = item.getValue();
			if (!this.containsKey(key)) {
				this.put(key, cmb);
			}
		}
	}

}
