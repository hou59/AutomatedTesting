package net.mooctest;

import static org.junit.Assert.*;

import org.junit.Test;

public class CMDTest1 {

	@Test
	public void test3() {
		CMD cmd = new CMD();
		CMD.Option.IntegerOption optionInt1 = new CMD.Option.IntegerOption('i', "test1");
		CMD.Option.IntegerOption optionInt2 = new CMD.Option.IntegerOption("test2");
		String[] arg1 = {"-i","abc"};
		cmd.addIntegerOption(optionInt2.longForm());
		cmd.addIntegerOption(optionInt1.shortForm().charAt(0),optionInt1.longForm());
		try {
			cmd.parse(arg1);
		} catch (CMD.OptionException e) {
			//e.printStackTrace();
			assertEquals("Illegal value 'abc' for option -i/--test1", e.getMessage());
		}
	}

	@Test
	public void test4() {
		CMD cmd = new CMD();
		CMD.Option.IntegerOption optionInt1 = new CMD.Option.IntegerOption('i', "test1");
		CMD.Option.IntegerOption optionInt2 = new CMD.Option.IntegerOption("test2");
		String[] arg1 = {"-test1"};
		cmd.addIntegerOption(optionInt2.longForm());
		cmd.addIntegerOption(optionInt1.shortForm().charAt(0),optionInt1.longForm());
		try {
			cmd.parse(arg1);
		} catch (CMD.OptionException e) {
			//e.printStackTrace();
			assertEquals("Illegal option: 't' in '-test1'", e.getMessage());
		}
	}

}

