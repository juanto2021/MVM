package org.tzi.mvm;

import java.util.HashSet;

public class CollectionCmb extends HashSet<Combination>{
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	// Si la combinacion no esta incluida la incluye
	@Override
	public boolean add(Combination e) {
		boolean suma=true;
		suma = contiene(e);
		if (!suma) {
			super.add(e);
		}
		return !suma;
	}

	// Se analiza si la coleccion contiene la combinacion de invariantes indicada	
	public boolean contiene(Combination e) {
		boolean contiene=false;
		for (Combination cmb : this) {
			if (cmb.getInvariants().containsAll(e.getInvariants())&&
					e.getInvariants().containsAll(cmb.getInvariants())) {
				contiene=true;
				break;
			}

		}
		return contiene;
	}

	// Se analiza si alguna de las combinaciones de la coleccion contiene la combinacion indicada
	public boolean sameContains(Combination e) {
		boolean containedIn=false;
		for (Combination cmb : this) {
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
		for (Combination cmb : this) {
			if (cmb.cmbContainedIn(e)){
				containsSame=true;
				break;
			}
		}
		return containsSame;
	}

}
