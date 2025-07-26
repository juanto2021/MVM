package org.tzi.use.kodkod.plugin;

import java.awt.Cursor;

import javax.swing.JOptionPane;

import org.tzi.kodkod.EventThreads;
import org.tzi.use.gui.main.MainWindow;
import org.tzi.use.kodkod.UseKodkodModelValidator;
import org.tzi.use.main.Session;
import org.tzi.use.runtime.gui.IPluginAction;
import org.tzi.use.runtime.gui.IPluginActionDelegate;
import org.tzi.use.uml.mm.MModel;
import org.tzi.use.uml.sys.MSystem;

public class StopCalcCmb implements IPluginActionDelegate {

	@Override
	public void performAction(IPluginAction pluginAction) {

		if(!pluginAction.getSession().hasSystem()){
			JOptionPane.showMessageDialog(pluginAction.getParent(),
					"No model present.", "No Model", JOptionPane.ERROR_MESSAGE);
			return;
		}
		Session session = pluginAction.getSession();

		MSystem mSystem= session.system();
		MModel mModel = mSystem.model();

		PluginModelFactory.INSTANCE.registerForSession(session);

		KodkodValidateCmd cmd = new KodkodValidateCmd();
		cmd.session=session;
		cmd.mSystem = mSystem;
		cmd.mModel = mModel;
		cmd.useShell = null;

		UseKodkodModelValidator uk = MainWindow.instance().getKodKod();
		if (uk!=null) {
			EventThreads threadGreedy = uk.getThreadGreedy();
			boolean calON=uk.getCalON();
			if (threadGreedy==null && calON==false) {
				JOptionPane.showMessageDialog(pluginAction.getParent(),
						"No calculations running.", "Stop searching for combinations", JOptionPane.ERROR_MESSAGE);
			}else {
				//			if (uk!=null) {
				// We activate the hourglass
				MainWindow.instance().setCursor(Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
				uk.stopThreadCmb();
				// We deactivate the hourglass		
				MainWindow.instance().setCursor(Cursor.getDefaultCursor());
			}
		}else {
			JOptionPane.showMessageDialog(pluginAction.getParent(),
					"No calculations running.", "Stop searching for combinations", JOptionPane.ERROR_MESSAGE);
		}
	}
	//		if (uk!=null) {
	//			// We activate the hourglass
	//			MainWindow.instance().setCursor(Cursor.getPredefinedCursor(Cursor.WAIT_CURSOR));
	//			uk.stopThreadCmb();
	//			// We deactivate the hourglass		
	//			MainWindow.instance().setCursor(Cursor.getDefaultCursor());
	//		}else {
	//			JOptionPane.showMessageDialog(pluginAction.getParent(),
	//					"No calculations running.", "Stop searching for combinations", JOptionPane.ERROR_MESSAGE);
	//		}
}

