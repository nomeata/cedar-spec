permit(
  principal,
  action,
  resource in a::""
) when {
  ((true && (true in ([principal, false] || (false == true)))) && action) && false
};
