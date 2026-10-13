module printing{

    theory Th{
        value: string
    }
    instance: Th = Th {value = "some value"}
     callPrint = () -> {Uniformal.print(instance.value)}
}
