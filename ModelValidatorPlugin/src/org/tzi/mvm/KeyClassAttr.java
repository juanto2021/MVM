package org.tzi.mvm;

import java.util.List;


import org.tzi.use.uml.mm.MClass;

public class KeyClassAttr {
	MClass mClass;
	List<KeyAttrInv> lAttr;
	public KeyClassAttr(MClass pClase, List<KeyAttrInv> pLattrInv) {
		this.mClass = pClase;
		this.lAttr = pLattrInv;
	}
}
