package org.tzi.mvm;


import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;

public class CollectionBitSet extends HashMap<String,BitSet>{
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	// Si la combinacion no esta incluida la incluye
	public boolean add(BitSet e) {
		boolean suma=false;
		if (!this.containsValue(e)) {
			this.put(e.toString(), e);
//			this.add(e);
			
			suma=true;
			return suma;
		}
		return suma;
	}

	// Se analiza si la coleccion contiene la combinacion de invariantes indicada	
	public boolean contiene(BitSet e) {
		boolean contiene=this.containsValue(e);
		return contiene;
	}

	// Se analiza si alguna de las combinaciones de la coleccion contiene la combinacion indicada
	public boolean sameContains(BitSet e) {
		boolean containedIn=this.containsValue(e);
		//		for (Entry<String, BitSet> item : this.entrySet()){
		//			BitSet cmb = item.getValue();
		//			if (cmb.e)){
		//				containedIn=true;
		//				break;
		//			}
		//		}
		return containedIn;
	}

	// Se analiza si alguna de las combinaciones de la coleccion esta contenida en la combinacion indicada
	public boolean sameContainedIn(BitSet e) {
		boolean containsSame=false;
		for (BitSet item : this.getList()){
//			BitSet cmb = item.getValue();
//			//			if (cmb.cmbContainedIn(e)){
			if (this.containsValue(e)){
				containsSame=true;
				break;
			}
		}		
		return containsSame;
	}
	public List<BitSet> getList(){
		List<BitSet> lCmbs = new ArrayList<>(this.values());
		return lCmbs;
	}

	public void addAll(CollectionBitSet colResSat) {
		for (Entry<String, BitSet> item : colResSat.entrySet()){
			String key = item.getKey();
			BitSet cmb = item.getValue();
			if (!this.containsKey(key)) {
				this.put(key, cmb);
			}
		}
	}

}
