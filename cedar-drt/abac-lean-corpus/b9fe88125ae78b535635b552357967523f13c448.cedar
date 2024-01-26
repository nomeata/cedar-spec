permit(
  principal,
  action,
  resource == a::""
) when {
  (true && (!(if principal then principal else (principal == true)))) && true
};
