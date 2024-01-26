permit(
  principal == a::"",
  action,
  resource in a::""
) when {
  ((true && (a::"ccc" == ([Ah000::Ahhgg::"\0\0", a::""].contains(principal)))) && principal) && principal
};
