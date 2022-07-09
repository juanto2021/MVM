package org.tzi.kodkod;

import org.tzi.kodkod.model.iface.IInvariant;

public class ResInv {
	String strInv;
	String strResultado;
	int intOrden;
	IInvariant invClass;
	
	public ResInv(String pStrInv, String pStrResultado, int pIntOrden, IInvariant pInvClass) {
		this.strInv = pStrInv;
		this.strResultado = pStrResultado;
		this.intOrden = pIntOrden;
		this.invClass = pInvClass;
	}
	public String getStrInv() {
		return strInv;
	}
	public void setStrInv(String strInv) {
		this.strInv = strInv;
	}
	public String getStrResultado() {
		return strResultado;
	}
	public void setStrResultado(String strResultado) {
		this.strResultado = strResultado;
	}
	public int getIntOrden() {
		return intOrden;
	}
	public void setInvariant(int intOrden) {
		this.intOrden = intOrden;
	}
	public IInvariant getInvClass() {
		return invClass;
	}
	public void setInvClass(IInvariant invClass) {
		this.invClass = invClass;
	}
	
}
