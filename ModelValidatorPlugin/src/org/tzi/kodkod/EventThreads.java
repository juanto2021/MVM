package org.tzi.kodkod;

import java.util.ArrayList;
import java.util.List;

/**
 * Abstract base class for all validation functionalities.
 * 
 * @author Hendrik Reitmann 
 *         modified by Juanto.
 */ 

public abstract class EventThreads extends Thread {
//	public class EventThreads extends Thread {

	private List<IEventStarted> listenersStarted = new ArrayList<>();
	private List<IEventEnded> listenersEnded = new ArrayList<>();

	public EventThreads() {
		this(false);
	}

	public EventThreads(final boolean isDaemon) {
		this.setDaemon(isDaemon);
	}

	public void run () {
		for (IEventStarted o : listenersStarted) {
			o.started();
		}

		operacionesRun();

		for (IEventEnded o : listenersEnded) {
			o.finalizado();
		}
	}

	public abstract void operacionesRun();// JG
//	public void operacionesRun() {};

	public void addListenerStarted(IEventStarted IEventStarted) {
		listenersStarted.add(IEventStarted);
	}

	public void removeListenerStarted(IEventStarted escuchador) {
		listenersStarted.remove(escuchador);
	}

	public void addListenerEnded(IEventEnded escuchador) {
		listenersEnded.add(escuchador);
	}

	public void removeListenerEnded(IEventEnded escuchador) {
		listenersEnded.remove(escuchador);
	}

	public interface IEventStarted {
		void started();
	}

	public interface IEventEnded {
		void finalizado();
	}
}

