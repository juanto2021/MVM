package org.tzi.mvm;

import java.util.List;
import org.tzi.use.uml.mm.MClass;
/**
 * Class for store attibutes/invariants relateds with a class
 * @author Juanto
 *
 */

public class KeyClassAttr {
	MClass mClass;
	List<KeyAttrInv> lAttr;
	public KeyClassAttr(MClass pClase, List<KeyAttrInv> pLattrInv) {
		this.mClass = pClase;
		this.lAttr = pLattrInv;
	}
	public MClass getClassAttr() {
		return mClass;
	}
	public void setClassAttr(MClass mClass) {
		this.mClass = mClass;
	}
	public List<KeyAttrInv> getlAttr() {
		return lAttr;
	}
	public void setlAttr(List<KeyAttrInv> lAttr) {
		this.lAttr = lAttr;
	}
	
}
