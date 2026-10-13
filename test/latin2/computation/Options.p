module Options {
	theory OptionTypes {
		include .sfol.SFOLEQND
	}

	theory UnsafeOptions {
		include OptionTypes
		include .exceptions.Exceptions
	}
}
