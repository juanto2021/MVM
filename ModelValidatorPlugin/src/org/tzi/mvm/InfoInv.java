package org.tzi.mvm;

import java.util.ArrayList;
import java.util.List;

import org.tzi.use.uml.mm.MAssociation;
import org.tzi.use.uml.mm.MAttribute;
/**
 * Attr y Assoc of one Invariant
 * @author utopi
 *
 */
public class InfoInv {
	List<MAttribute> lAttr = new ArrayList<MAttribute>();
	List<MAssociation> lAssoc = new ArrayList<MAssociation>();
	public InfoInv(List<MAttribute> lAttr, List<MAssociation> lAssoc) {
		super();
		this.lAttr = lAttr;
		this.lAssoc = lAssoc;
	}
	public InfoInv() {
		lAttr = new ArrayList<MAttribute>();
		lAssoc = new ArrayList<MAssociation>();
	}
	public List<MAttribute> getlAttr() {
		return lAttr;
	}
	public void setlAttr(List<MAttribute> lAttr) {
		this.lAttr = lAttr;
	}
	public List<MAssociation> getlAssoc() {
		return lAssoc;
	}
	public void setlAssoc(List<MAssociation> lAssoc) {
		this.lAssoc = lAssoc;
	}
	
}
