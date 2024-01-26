@A("6\06")
permit(
  principal in K::"",
  action == Action::"0003",
  resource is A002 in m::""
) when {
  false
};
