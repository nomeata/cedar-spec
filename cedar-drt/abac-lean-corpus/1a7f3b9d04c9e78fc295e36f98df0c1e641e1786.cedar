permit(
  principal == a::"jj",
  action in [Action::"action"],
  resource in a::"jj"
) when {
  ((true && (a::"ccc" == ([Ah000::Ahhgg::"\0\0", a::"jj"].contains(principal)))) && context) && a::"jj"
};
