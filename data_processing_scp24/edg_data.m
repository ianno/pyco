iter = 10000;
load('EDG_SINGLE_LIB16');
load('EDG_SINGLE_LIB24');
load('EDG_SINGLE_LIB32');

%only first column
A = EDG_SINGLE_LIB16(:,1);
B = EDG_SINGLE_LIB24(:,1);
C = EDG_SINGLE_LIB32(:,1);

figure;
hold;
stata = bootstrp(iter, @mean, A);
histogram(stata);
statb = bootstrp(iter, @mean, B);
histogram(statb);
statc = bootstrp(iter, @mean, C);
histogram(statc);
% figure;
% hold;
% plot(ksdensity(statb))
% mean_a = mean(A)
mean_a = mean(stata)
% mean_b = mean(B)
mean_b = mean(statb)
% mean_c = mean(C)
mean_c = mean(statc)
meanci_a = bootci(iter, @mean, A)
meanci_b = bootci(iter, @mean, B)
meanci_c = bootci(iter, @mean, C)
%median is very bad
figure;
hold;
stat = bootstrp(iter, @median, A);
histogram(stat);
stat = bootstrp(iter, @median, B);
histogram(stat);
stat = bootstrp(iter, @median, C);
histogram(stat);


med_a = bootci(iter, @median, A);
med_b = bootci(iter, @median, B);
med_c = bootci(iter, @median, C);