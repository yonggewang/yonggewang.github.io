/*This code is by Yongge Wang, November 2015.
the code is for RLCE scheme security verification
Specifically, this code is used to show that filtration 
attacks will not work against RCLE schemes.
this code requries NTL library which could be obtained
at http://shoup.net/ntl/ 
*/


#include <NTL/ZZ.h>
#include <NTL/ZZ_pXFactoring.h>
#include <NTL/ZZ_pEX.h>
#include <NTL/matrix.h>
#include <NTL/vec_vec_ZZ_pE.h>
#include <NTL/mat_ZZ_pE.h>
#include <iostream>
#include <fstream>

using namespace std;
using namespace NTL;

void defineAm(ZZ_pE [8][8], ZZ_pE [1][8]);
void inverseMat (ZZ_pE K[8][8], ZZ_pE Ki[8][8]);
void multipyMat(ZZ_pE [8][8], ZZ_pE [8][8], ZZ_pE [8][8]);


ofstream out("results.txt");

int main()
{
	//60 bit security: n=360, k=240, t=90
	//80 bit security: n=560, k=380, t=90
	const int n = 560;
	const int k = 380;
	const int t = 90;
	const int m = 10; //finite field is of size q=2^m

	ZZ_p::init(ZZ(2)); // define GF(2)
	ZZ_pX P;
	P.SetLength(m+1);
	P[0] = 1;
	P[3] = 1;
	P[10] = 1;
	//P = 1 + X ^ 3 + X^{ 10 } is a primitive polynomial
	// and X is then a primitive element

	ZZ_pX alphaP;
	alphaP.SetLength(m);
	alphaP[1] = 1;

	//if need irreducible polynomial.
	//BuildIrred(P, m); // generate an irreducible polynomial P of degree m over GF(2)

	ZZ_pE::init(P); // define GF(2^10) 
	ZZ_pE alpha; // generator for the filed
	alpha = ZZ_pE();
	conv(alpha, alphaP);// alpha = x, is the primitive element that generates all fileds

	ZZ_pEX unit, g, h;  // declare polynomials over GF(2^10), g is the  generator
	                    //polynomial for RS code
	unit.SetLength(2);
	unit[1] = 1;
	g.SetLength(n - k + 1);
	h.SetMaxLength(n-k+1);

	g = unit - 1;
	h = alpha;
	for (int i = 1; i < n - k; i++) {
		g = g*(unit-h);
		h = h*alpha;
	}
	//out << deg(g) << endl;

	Mat<ZZ_pE> G;
	G.SetDims(k, n);
	for (int i = 0; i < k; i++) {
		for (int j = i; j < n-k+i+1; j++) {
			G[i][j] = g[j-i];
		}
	}

	Mat<ZZ_pE> C; // C will be the random columns that will be inserted
	C.SetDims(k, n);
	for (int i = 0; i < k; i++) {
		for (int j = 0; j < n; j++) {
			random(C[i][j]);
		}
	}

	Mat<ZZ_pE> G1; // G1 is the mix of G and C  
	G1.SetDims(k, 2*n);
	for (int i = 0; i < k; i++) {
		for (int j = 0; j < n; j++) {
			G1[i][2*j] = G[i][j];
			G1[i][2*j+1] = C[i][j];
		}
	}

	Mat<ZZ_pE> A; 
	A.SetDims(2*n, 2 * n);
	for (int i = 0; i < n; i++) {
		random(A[2*i][2*i]);
		random(A[2 * i][2 * i+1]);
		random(A[2 * i+1][2 * i]);
		random(A[2 * i+1][2 * i+1]);
	}

	Mat<ZZ_pE> S;
	S.SetDims(k,k);
	for (int i = 0; i < k; i++) {
		for (int j = 0; j < k; j++) {
			random(S[i][j]);
		}
	}

	Mat<ZZ_pE> pubK; // pubK is the public key 
	pubK.SetDims(k, 2 * n);
	pubK = S*G1 * A;

	Mat<ZZ_pE> prodK; // pubK is the public key 
	prodK.SetDims(k*k, 2 * n);
	int row = 0;
	for (int i = 0; i < k; i++) {
		for (int j = 0; j < k; j++) {
			for (int ii = 0; ii < 2 * n; ii++) {
				prodK[row][ii] = pubK[i][ii] * pubK[j][ii];
			}
			row = row + 1;
		}
	}

	out << "the following is the informaiton. There are 2n= " << endl;
	out << 2 * n << endl;
	out << " rows and k^2= " << endl;
	out << k * k << endl;
	out << " columns\n\n" << endl;

	int badCol = 0;

	Mat<ZZ_pE> prodKreduced; 
	prodKreduced.SetDims(2*n-1, k*k);
	for (int i = 0; i < 2*n; i++) {
		int jj = 0;
		for (int j = 0; j < 2 * n; j++) {
			if (i != j) { 
				for (int ii = 0; ii < k*k; ii++) {
					prodKreduced[jj][ii] = prodK[ii][j];
				}
				jj = jj + 1;
			}
		}
		int rank;
		rank = gauss(prodKreduced);
		if (rank < 2*n) {
			badCol = badCol + 1;
			out << "if the column " << endl;
			out << i << endl;
			out << " is deleted, then the rank is: " << endl;
			out << rank << endl;
			out << "\n\n " << endl;
		}
	}


	//out << C << endl;


	//Matrix Ki = K inverse 
	//inverseMat(K,Ki);


}

//Define Am
void defineAm(ZZ_pE Am[8][8], ZZ_pE a[1][8]){
	for (int j=0; j<8; j++)
		Am[0][j]=a[0][j];

	for (int i=1; i<8; i++)
		negate(Am[i][0], a[0][i]);

	for (int i=1; i<8; i++)
		Am[i][i]=a[0][0];

	Am[2][4]=Am[3][7]=Am[5][6]=a[0][1];
	Am[3][5]=Am[4][1]=Am[6][7]=a[0][2];
	Am[4][6]=Am[5][2]=Am[7][1]=a[0][3];
	Am[1][2]=Am[5][7]=Am[6][3]=a[0][4];
	Am[2][3]=Am[6][1]=Am[7][4]=a[0][5];
	Am[1][5]=Am[3][4]=Am[7][2]=a[0][6];
	Am[1][3]=Am[2][6]=Am[4][5]=a[0][7];

	negate(Am[4][2], a[0][1]);
	negate(Am[6][5], a[0][1]);
	negate(Am[7][3], a[0][1]);

	negate(Am[1][4], a[0][2]);
	negate(Am[5][3], a[0][2]);
	negate(Am[7][6], a[0][2]);

	negate(Am[1][7], a[0][3]);
	negate(Am[2][5], a[0][3]);
	negate(Am[6][4], a[0][3]);

	negate(Am[2][1], a[0][4]);
	negate(Am[3][6], a[0][4]);
	negate(Am[7][5], a[0][4]);

	negate(Am[1][6], a[0][5]);
	negate(Am[3][2], a[0][5]);
	negate(Am[4][7], a[0][5]);

	negate(Am[2][7], a[0][6]);
	negate(Am[4][3], a[0][6]);
	negate(Am[5][1], a[0][6]);

	negate(Am[3][1], a[0][7]);
	negate(Am[5][4], a[0][7]);
	negate(Am[6][2], a[0][7]);

}


//Multiply 2 Matrices
void multipyMat(ZZ_pE M1[8][8], ZZ_pE M2[8][8], ZZ_pE temp[8][8]){
	ZZ_pE r, sum;
	for (int i = 0; i < 8; i++) {
      for (int j = 0; j < 8; j++) {
        for (int k = 0; k < 8; k++) {
          //sum = sum + M1[i][k]*M2[k][j];
			mul(r,M1[i][k],M2[k][j]);
			add(sum,sum,r);
			//sum+=r;
        }
        temp[i][j] = sum;
        sum = 0;
      }
    }
}


//Matrix Inverse
void inverseMat (ZZ_pE K[8][8], ZZ_pE Ki[8][8]){
	ZZ_pE determinant;
	for(int i=0;i<8;i++)
		determinant = determinant + (K[0][i]*(K[1][(i+1)%8] * K[2][(i+2)%8] - K[1][(i+2)%8]*K[2][(i+1)%8]));
	if(determinant==0)
		cout<<"Inverse does not exist (Determinant=0).\n";
	else
	{
		for(int i=0;i<8;i++)
			for(int j=0;j<8;j++)
				Ki[i][j] = (K[(i+1)%8][(j+1)%8] * K[(i+2)%8][(j+2)%8]) - (K[(i+1)%8][(j+2)%8] * K[(i+2)%8][(j+1)%8])/ determinant;
	}
}