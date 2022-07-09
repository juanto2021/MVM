	package org.tzi.use.kodkod.plugin;
	
	import java.io.PrintWriter;
	import java.io.StringWriter;
	
	import javax.swing.JOptionPane;
	
	import org.apache.commons.configuration.Configuration;
	import org.apache.commons.configuration.ConfigurationException;
	import org.tzi.kodkod.model.iface.IModel;
	import org.tzi.use.gui.main.MainWindow;
	import org.tzi.use.kodkod.UseKodkodModelValidator;
	import org.tzi.use.kodkod.plugin.gui.ModelValidatorConfigurationWindowJuanto;
	import org.tzi.use.main.Session;
	import org.tzi.use.runtime.gui.IPluginAction;
	import org.tzi.use.runtime.gui.IPluginActionDelegate;
	import org.tzi.use.uml.mm.MModel;
	import org.tzi.use.uml.sys.MSystem;
	
	/**
	 * Action-Class to extend the toolbar with a button to call the model validator
	 * with a configuration file.
	 * 
	 * @author Juanto
	 * 
	 */
	public class KodkodValidateJuantoAction  implements IPluginActionDelegate {
	
		@Override
		public void performAction(IPluginAction pluginAction) {
			// Llama al validador Alternativo
	
			if(!pluginAction.getSession().hasSystem()){
				JOptionPane.showMessageDialog(pluginAction.getParent(),
						"No model present.", "No Model", JOptionPane.ERROR_MESSAGE);
				return;
			}
			Session session = pluginAction.getSession();
	
			MSystem mSystem= session.system();
			MModel mModel = mSystem.model();
	
			PluginModelFactory.INSTANCE.registerForSession(session);
	
			IModel model = PluginModelFactory.INSTANCE.getModel(mModel);
	
			KodkodValidateCmd cmd = new KodkodValidateCmd();
			cmd.session=session;
			cmd.mSystem = mSystem;
			cmd.mModel = mModel;
			cmd.useShell = null;
	
			ModelValidatorConfigurationWindowJuanto modelValidatorConfigurationWindow = 
					new ModelValidatorConfigurationWindowJuanto(MainWindow.instance(), model, mModel.filename());
	
			Configuration config = modelValidatorConfigurationWindow.getChosenConfiguration();
	
			StringWriter errorBuffer = new StringWriter();
			try {
				cmd.configureModel(config, new PrintWriter(errorBuffer, true));
			} catch (ConfigurationException e) {
				e.printStackTrace();
			}
	
			UseKodkodModelValidator uk = new UseKodkodModelValidator(session);
			uk.validateVariable(model, mModel,session);
	
		}
	
	}
