permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (ip(true))) && a::""
};
