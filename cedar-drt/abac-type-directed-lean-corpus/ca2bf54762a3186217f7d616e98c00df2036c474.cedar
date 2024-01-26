permit(
  principal,
  action,
  resource
) when {
  (true && ((a::"\0-" in [principal]) == false)) && (false == false)
};
