package org.tzi.mvm;

import org.tzi.use.uml.mm.MAttribute;
import org.tzi.use.uml.mm.MClassInvariant;
import java.util.List;

public class KeyAttrInv {
	MAttribute attr;
	List<MClassInvariant> lInv;
	public KeyAttrInv(MAttribute pAttr, List<MClassInvariant> pLinv) {
		this.attr = pAttr;
		this.lInv = pLinv;

	}
}
