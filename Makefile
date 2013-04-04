INCLUDE=-i . -i /usr/share/agda-stdlib

compile:
	agda $(INCLUDE) RGref.agda

html:
	agda --html $(INCLUDE) RGref.agda
