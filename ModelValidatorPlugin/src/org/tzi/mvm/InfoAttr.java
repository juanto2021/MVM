package org.tzi.mvm;

import java.util.ArrayList;
import java.util.List;

import org.tzi.use.uml.mm.MClassInvariant;

/**
 * Invariants of attribute
 * @author Juanto
 *
 */
public class InfoAttr {
	List<MClassInvariant> lInv = new ArrayList<MClassInvariant>();

	public InfoAttr(List<MClassInvariant> lInv) {
		this.lInv = lInv;
	}

	public List<MClassInvariant> getlInv() {
		return lInv;
	}

	public void setlInv(List<MClassInvariant> lInv) {
		this.lInv = lInv;
	}

}
