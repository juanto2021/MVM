package org.tzi.mvm;

public class LinkWizard {
	private String object;
	private String nomClass;
	private String connectedTo;
	private String ofClass;
	private String assocEnd;
	private String multiSpecified;
	private String cause;
	private String fullMessage;

	public LinkWizard() {
		super();
		this.object = "";
		this.nomClass = "";
		this.connectedTo = "";
		this.ofClass = "";
		this.assocEnd = "";
		this.multiSpecified = "";
		this.cause = "";
		this.fullMessage = "";
	}

	public LinkWizard(String object, String nomClass, String connectedTo, String ofClass,
			String assocEnd, String multiSpecified, String cause, String fullMessage) {
		super();
		this.object = object;
		this.nomClass = nomClass;
		this.connectedTo = connectedTo;
		this.ofClass = ofClass;
		this.assocEnd = assocEnd;
		this.multiSpecified = multiSpecified;
		this.cause = cause;
		this.fullMessage = fullMessage;		
	}

	public String getObject() {
		return object;
	}
	public void setObject(String object) {
		this.object = object;
	}
	public String getNomClass() {
		return nomClass;
	}
	public void setNomClass(String nomClass) {
		this.nomClass = nomClass;
	}
	public String getConnectedTo() {
		return connectedTo;
	}
	public void setConnectedTo(String connectedTo) {
		this.connectedTo = connectedTo;
	}
	public String getOfClass() {
		return ofClass;
	}
	public void setOfClass(String ofClass) {
		this.ofClass = ofClass;
	}
	public String getAssocEnd() {
		return assocEnd;
	}
	public void setAssocEnd(String assocEnd) {
		this.assocEnd = assocEnd;
	}
	public String getMultiSpecified() {
		return multiSpecified;
	}
	public void setMultiSpecified(String multiSpecified) {
		this.multiSpecified = multiSpecified;
	}

	public String getCause() {
		return cause;
	}

	public void setCause(String cause) {
		this.cause = cause;
	}

	public String getFullMessage() {
		return fullMessage;
	}

	public void setFullMessage(String fullMessage) {
		this.fullMessage = fullMessage;
	}

}
