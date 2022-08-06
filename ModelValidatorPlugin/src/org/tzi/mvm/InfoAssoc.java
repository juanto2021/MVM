package org.tzi.mvm;

import java.util.ArrayList;
import java.util.List;

import org.tzi.use.uml.mm.MClassInvariant;

/**
 * Invariants of association
 * @author Juanto
 *
 */
public class InfoAssoc {
	List<MClassInvariant> lInv = new ArrayList<MClassInvariant>();

	public InfoAssoc(List<MClassInvariant> lInv) {
		super();
		this.lInv = lInv;
	}

	public List<MClassInvariant> getlInv() {
		return lInv;
	}

	public void setlInv(List<MClassInvariant> lInv) {
		this.lInv = lInv;
	}
	
}
