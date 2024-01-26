permit(
  principal,
  action,
  resource
) when {
  (true && ((a::"\0" in [principal]) == false)) && (a::"\0" == a::"\0")
};
