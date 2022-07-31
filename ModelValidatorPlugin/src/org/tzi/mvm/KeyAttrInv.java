package org.tzi.mvm;

import org.tzi.use.uml.mm.MAttribute;
import org.tzi.use.uml.mm.MClassInvariant;

import java.util.Collection;
import java.util.List;
/**
 * Class for store invariants relates with one attribute
 * @author Juanto
 *
 */
public class KeyAttrInv {
	MAttribute attr;
	List<MClassInvariant> lInv;
	public KeyAttrInv(MAttribute pAttr, List<MClassInvariant> pLinv) {
		this.attr = pAttr;
		this.lInv = pLinv;
	}
	public MAttribute getAttr() {
		return attr;
	}
	public void setAttr(MAttribute attr) {
		this.attr = attr;
	}
	public List<MClassInvariant> getlInv() {
		return lInv;
	}
	public void setlInv(List<MClassInvariant> lInv) {
		this.lInv = lInv;
	}
	
}
